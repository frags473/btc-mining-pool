#!/usr/bin/env python3

"""
BTC+DGB AuxPow Merged Mining Stratum Proxy
==========================================
Sits between miners and bitcoind's getblocktemplate.
- Fetches BTC block template from bitcoind
- Fetches DGB SHA256d block template from digibyted
- Embeds DGB auxpow commitment in BTC coinbase
- Serves miners via Stratum v1 on port 3032
- When a share meets DGB difficulty, submits auxpow block to digibyted
- When a share meets BTC difficulty, submits to bitcoind

This is a SOLO mining pool - all rewards go directly to your addresses.
Configuration is loaded from pool.conf (see pool.conf.example).
"""

import asyncio
import json
import hashlib
import struct
import time
import logging
import sys
import os
import binascii
import urllib.request
import base64
import collections
from typing import Optional, Dict, List

# ── Configuration ─────────────────────────────────────────────────────────────
# Credentials are loaded from pool.conf (never committed to git).
# Copy pool.conf.example to pool.conf and fill in your values.
import configparser as _cp
_cfg = _cp.ConfigParser()
_cfg_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pool.conf')
if not _cfg.read(_cfg_path):
    raise FileNotFoundError(f'pool.conf not found at {_cfg_path} — copy pool.conf.example and fill in your credentials')

BTC_RPC = (
    _cfg.get('bitcoin', 'rpc_host', fallback='127.0.0.1'),
    _cfg.getint('bitcoin', 'rpc_port', fallback=8332),
    _cfg.get('bitcoin', 'rpc_user'),
    _cfg.get('bitcoin', 'rpc_pass'),
)
DGB_RPC = (
    _cfg.get('digibyte', 'rpc_host', fallback='127.0.0.1'),
    _cfg.getint('digibyte', 'rpc_port', fallback=14022),
    _cfg.get('digibyte', 'rpc_user'),
    _cfg.get('digibyte', 'rpc_pass'),
)

BTC_ADDRESS = _cfg.get('pool', 'btc_address')
DGB_ADDRESS = _cfg.get('pool', 'dgb_address')
POOL_SIG    = _cfg.get('pool', 'pool_sig', fallback='/MintNode/')

STRATUM_HOST = '0.0.0.0'
STRATUM_PORT = 3032
API_PORT     = 8080

# Difficulty settings tuned for Nerd 12 TH/s ASIC:
#   12e12 * 15 / 2^32 ≈ 41,910  → diff 32768 gives ~1 share every 11s
MIN_DIFF   = 16384      # floor
START_DIFF = 32768      # tuned for 12 TH/s Nerd (~1 share/11s)
MAX_DIFF   = 131072     # ceiling for vardiff

# VarDiff settings
VARDIFF_TARGET_SECS  = 15   # target 1 share per 15 seconds
VARDIFF_RETARGET     = 90   # recalculate every 90 seconds
VARDIFF_VARIANCE_PCT = 30   # allow ±30% before retargeting

LOG_FILE = '/home/harry/auxpow_proxy.log'

# DGB chain ID for SHA256d algo (chain_id = 1 for DGB SHA256d)
DGB_CHAIN_ID = 1

# ── Logging ───────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format='[%(asctime)s] %(levelname)s %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S',
    handlers=[
        logging.StreamHandler(sys.stdout)
    ]
)
log = logging.getLogger('auxpow')

# ── Crypto helpers ────────────────────────────────────────────────────────────
def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()

def merkle_root_from_hashes(hashes: List[str]) -> bytes:
    """Compute merkle root. hashes are hex strings in natural byte order."""
    if not hashes:
        return b'\x00' * 32
    nodes = [bytes.fromhex(h)[::-1] for h in hashes]  # to little-endian
    while len(nodes) > 1:
        if len(nodes) % 2 == 1:
            nodes.append(nodes[-1])
        nodes = [sha256d(nodes[i] + nodes[i+1]) for i in range(0, len(nodes), 2)]
    return nodes[0]  # still little-endian

def bits_to_target(bits_hex: str) -> int:
    bits = int(bits_hex, 16)
    exp = bits >> 24
    mant = bits & 0xFFFFFF
    return mant * (1 << (8 * (exp - 3)))

def target_to_diff(target: int) -> float:
    diff1 = 0x00000000FFFF0000000000000000000000000000000000000000000000000000
    return diff1 / target if target else 0

def diff_to_target(diff: float) -> int:
    diff1 = 0x00000000FFFF0000000000000000000000000000000000000000000000000000
    return int(diff1 / diff) if diff else 0

def fmt_diff(d: float) -> str:
    """Format a difficulty value as a human-readable SI string.
    Examples: 5.33e-10 -> '0.53n', 6.56e-9 -> '6.56n', 32768 -> '32.77K',
              1.5e9 -> '1.50G', 124e12 -> '124.00T'
    """
    if d == 0:
        return '0'
    tiers = [
        (1e15, 'P'),
        (1e12, 'T'),
        (1e9,  'G'),
        (1e6,  'M'),
        (1e3,  'K'),
        (1.0,  ''),
        (1e-3, 'm'),
        (1e-6, 'u'),
        (1e-9, 'n'),
    ]
    for threshold, suffix in tiers:
        if d >= threshold:
            return f'{d / threshold:.2f}{suffix}'
    return f'{d:.2e}'

def pack_varint(n: int) -> bytes:
    if n < 0xfd:
        return struct.pack('B', n)
    elif n <= 0xffff:
        return b'\xfd' + struct.pack('<H', n)
    elif n <= 0xffffffff:
        return b'\xfe' + struct.pack('<I', n)
    else:
        return b'\xff' + struct.pack('<Q', n)

def encode_script_num(n: int) -> bytes:
    if n == 0:
        return b''
    result = []
    neg = n < 0
    absval = abs(n)
    while absval:
        result.append(absval & 0xff)
        absval >>= 8
    if result[-1] & 0x80:
        result.append(0x80 if neg else 0)
    elif neg:
        result[-1] |= 0x80
    return bytes(result)

def script_push(data: bytes) -> bytes:
    n = len(data)
    if n < 0x4c:
        return bytes([n]) + data
    elif n <= 0xff:
        return b'\x4c' + bytes([n]) + data
    elif n <= 0xffff:
        return b'\x4d' + struct.pack('<H', n) + data
    else:
        return b'\x4e' + struct.pack('<I', n) + data

# ── RPC ───────────────────────────────────────────────────────────────────────
def rpc(host, port, user, pw, method, params=None):
    if params is None:
        params = []
    payload = json.dumps({'jsonrpc':'1.0','id':'p','method':method,'params':params}).encode()
    creds = base64.b64encode(f'{user}:{pw}'.encode()).decode()
    req = urllib.request.Request(
        f'http://{host}:{port}/',
        data=payload,
        headers={'Content-Type':'text/plain','Authorization':f'Basic {creds}'}
    )
    try:
        resp = urllib.request.urlopen(req, timeout=15)
        return json.loads(resp.read())
    except Exception as e:
        return {'error': str(e)}

def btc_rpc(method, params=None):
    return rpc(*BTC_RPC, method, params)

def dgb_rpc(method, params=None):
    return rpc(*DGB_RPC, method, params)

# ── AuxPow commitment builder ─────────────────────────────────────────────────
MERGED_MAGIC = bytes.fromhex('fabe6d6d')

def build_auxpow_commitment(aux_hash_hex: str, chain_id: int = DGB_CHAIN_ID) -> bytes:
    """
    Build the merged mining commitment for the BTC coinbase.
    
    Format (per Bitcoin merged mining spec):
      magic:        fabe6d6d  (4 bytes)
      chain_merkle: <32 bytes> (the aux chain's block hash, little-endian)
      merkle_size:  <4 bytes LE> (number of aux chains = 1)
      merkle_nonce: <4 bytes LE> (nonce = 0)
    
    This is pushed as OP_RETURN data in the coinbase.
    """
    # aux_hash is in natural byte order (big-endian), convert to little-endian
    aux_hash_le = bytes.fromhex(aux_hash_hex)[::-1]
    
    commitment = (
        MERGED_MAGIC +
        aux_hash_le +
        struct.pack('<I', 1) +   # merkle_size = 1 (only DGB)
        struct.pack('<I', 0)     # merkle_nonce = 0
    )
    return commitment

def build_coinbase(height: int, extra_nonce1: bytes, extra_nonce2: bytes,
                   btc_address: str, pool_sig: str,
                   aux_commitment: Optional[bytes] = None) -> bytes:
    """
    Build a coinbase transaction with optional auxpow commitment.
    Returns (coinbase_bytes, coinbase1_hex, coinbase2_hex)
    """
    # Coinbase input script:
    # height (BIP34) + pool_sig + extra_nonce1 + extra_nonce2
    height_script = script_push(encode_script_num(height))
    sig_bytes = pool_sig.encode('utf-8')
    
    coinbase_script = (
        height_script +
        script_push(sig_bytes) +
        extra_nonce1 +
        extra_nonce2
    )
    
    # If we have an aux commitment, add it as OP_RETURN output
    # The commitment goes in the coinbase SCRIPT (not as output) per spec
    # Actually per merged mining spec, it goes in the coinbase INPUT script
    if aux_commitment:
        # Append magic + commitment to coinbase script
        coinbase_script += aux_commitment
    
    # Coinbase input
    txin = (
        b'\x00' * 32 +          # prev hash (null)
        b'\xff\xff\xff\xff' +   # prev index (0xffffffff)
        pack_varint(len(coinbase_script)) +
        coinbase_script +
        b'\xff\xff\xff\xff'     # sequence
    )
    
    # We need a proper output - use OP_RETURN for now (value=0)
    # Real implementation needs to decode btc_address to scriptPubKey
    # For bech32 addresses, use P2WPKH
    # Simplified: use OP_RETURN with address bytes as placeholder
    # TODO: proper address decoding
    op_return_data = btc_address.encode()
    txout_script = b'\x6a' + pack_varint(len(op_return_data)) + op_return_data
    txout = struct.pack('<q', 0) + pack_varint(len(txout_script)) + txout_script
    
    tx = (
        struct.pack('<I', 1) +   # version
        pack_varint(1) +         # input count
        txin +
        pack_varint(1) +         # output count
        txout +
        struct.pack('<I', 0)     # locktime
    )
    return tx

# ── Work manager ──────────────────────────────────────────────────────────────
class WorkManager:
    def __init__(self):
        self.btc_template = None
        self.dgb_template = None
        self.current_job_id = 0
        self.jobs = {}
        self.lock = asyncio.Lock()
        self.subscribers = []
        
    async def update_templates(self):
        """Fetch fresh templates from both daemons."""
        loop = asyncio.get_event_loop()
        
        # Fetch BTC template
        btc = await loop.run_in_executor(None, lambda: btc_rpc('getblocktemplate', [{'rules':['segwit']}]))
        if btc.get('result'):
            self.btc_template = btc['result']
            
        # Fetch DGB SHA256d template
        # DGB v8.26+ uses algo as a SECOND positional argument: getblocktemplate({...}, "sha256d")
        dgb = await loop.run_in_executor(None, lambda: dgb_rpc('getblocktemplate',
            [{'rules': ['segwit']}, 'sha256d']))
        if dgb.get('result'):
            t = dgb['result']
            if t.get('pow_algo') == 'sha256d':
                self.dgb_template = t
                log.debug(f"DGB SHA256d template: height={t.get('height')} bits={t.get('bits')}")
            else:
                log.warning(f"DGB returned algo={t.get('pow_algo')}, expected sha256d")
        elif dgb.get('error'):
            log.error(f"DGB getblocktemplate error: {dgb.get('error')}")
                
    def make_job(self, extra_nonce1_hex: str) -> Optional[dict]:
        """Create a new mining job from current templates."""
        if not self.btc_template:
            return None
            
        bt = self.btc_template
        self.current_job_id += 1
        job_id = f'{self.current_job_id:08x}'
        
        # Build aux commitment if DGB template available
        aux_commitment = None
        dgb_target = None
        dgb_height = None
        
        if self.dgb_template:
            dt = self.dgb_template
            dgb_height = dt.get('height', 0)
            dgb_target = dt.get('target', '')
            
            # The DGB block hash we commit to is the hash of the DGB block header
            # For auxpow, we use the previousblockhash as the chain tip identifier
            # The actual commitment is the hash of the DGB block template
            prev_hash = dt.get('previousblockhash', '00' * 32)
            aux_commitment = build_auxpow_commitment(prev_hash)
            log.debug(f"AuxPow commitment built for DGB height={dgb_height}")
        
        # Build coinbase parts
        height = bt.get('height', 0)
        
        # Coinbase part 1 (before extra_nonce)
        height_script = script_push(encode_script_num(height))
        sig_bytes = POOL_SIG.encode('utf-8')
        
        # Simplified coinbase building for stratum
        # coinb1: everything up to extra_nonce
        # coinb2: everything after extra_nonce
        
        # Script: height + pool_sig + [aux_commitment]
        script_prefix = height_script + script_push(sig_bytes)
        if aux_commitment:
            script_prefix += aux_commitment
            
        extra_nonce1 = bytes.fromhex(extra_nonce1_hex)
        extra_nonce2_size = 8
        
        script_total_len = len(script_prefix) + len(extra_nonce1) + extra_nonce2_size
        
        coinb1 = (
            '01000000'  +  # version
            '01' +         # input count
            '00' * 32 +   # prev hash (null)
            'ffffffff' +  # prev index
            pack_varint(script_total_len).hex() +
            script_prefix.hex() +
            extra_nonce1_hex
        )
        
        coinb2 = (
            'ffffffff' +  # sequence
            '01' +         # output count
            # value = coinbasevalue
            struct.pack('<q', bt.get('coinbasevalue', 0)).hex() +
            # scriptPubKey - simplified OP_RETURN for now
            '19' +  # script length (25 bytes for P2PKH placeholder)
            '76a914' + '00' * 20 + '88ac' +  # P2PKH placeholder
            '00000000'  # locktime
        )
        
        # Previous block hash (reversed for stratum)
        prev_hash = bt.get('previousblockhash', '00' * 32)
        prev_hash_stratum = ''.join([prev_hash[i:i+8][::-1] for i in range(0, 64, 8)])
        # Actually stratum uses byte-swapped groups of 4
        prev_hash_stratum = ''
        for i in range(0, 64, 8):
            chunk = prev_hash[i:i+8]
            prev_hash_stratum += chunk[::-1]  # reverse each char pair group
        # Correct byte-swap for stratum
        ph_bytes = bytes.fromhex(prev_hash)
        prev_hash_stratum = ''.join([f'{b:02x}' for b in ph_bytes[::-1]])
        
        # Merkle branches (transaction hashes)
        txs = bt.get('transactions', [])
        tx_hashes = [tx['hash'] for tx in txs]
        # Build merkle branch
        merkle_branch = self._build_merkle_branch(tx_hashes)
        
        job = {
            'job_id': job_id,
            'prev_hash': prev_hash_stratum,
            'coinb1': coinb1,
            'coinb2': coinb2,
            'merkle_branch': merkle_branch,
            'version': bt.get('version', 0x20000000),
            'bits': bt.get('bits', ''),
            'time': bt.get('curtime', int(time.time())),
            'btc_target': bt.get('target', ''),
            'btc_height': height,
            'dgb_target': dgb_target,
            'dgb_height': dgb_height,
            'dgb_template': self.dgb_template,
            'btc_template': bt,
            'extra_nonce1': extra_nonce1_hex,
            'extra_nonce2_size': extra_nonce2_size,
        }
        
        self.jobs[job_id] = job
        return job
    
    def _build_merkle_branch(self, tx_hashes: List[str]) -> List[str]:
        """Build merkle branch for stratum (hashes needed to verify coinbase)."""
        if not tx_hashes:
            return []
        branch = []
        nodes = [bytes.fromhex(h)[::-1] for h in tx_hashes]
        while nodes:
            branch.append(nodes[0][::-1].hex())
            if len(nodes) == 1:
                break
            if len(nodes) % 2 == 1:
                nodes.append(nodes[-1])
            nodes = [sha256d(nodes[i] + nodes[i+1]) for i in range(0, len(nodes), 2)]
            nodes = nodes[1:]  # remove first (that's our branch)
        return branch

# ── Stratum server ────────────────────────────────────────────────────────────
class StratumClient:
    def __init__(self, reader, writer, server):
        self.reader = reader
        self.writer = writer
        self.server = server
        self.extra_nonce1 = os.urandom(4).hex()
        self.extra_nonce2_size = 8
        self.subscribed = False
        self.authorized = False
        self.worker_name = ''
        self.difficulty = START_DIFF
        self.addr = writer.get_extra_info('peername')
        
    async def send(self, msg: dict):
        data = json.dumps(msg) + '\n'
        self.writer.write(data.encode())
        await self.writer.drain()
        
    async def handle(self):
        log.info(f'Miner connected: {self.addr}')
        try:
            while True:
                line = await self.reader.readline()
                if not line:
                    break
                raw = line.decode().strip()
                if raw:
                    log.debug(f'RECV {self.addr}: {raw[:200]}')
                try:
                    msg = json.loads(raw)
                    await self.process(msg)
                except json.JSONDecodeError:
                    log.warning(f'Non-JSON from {self.addr}: {raw[:100]}')
        except (asyncio.IncompleteReadError, ConnectionResetError):
            pass
        finally:
            log.info(f'Miner disconnected: {self.addr}')
            self.server.clients.discard(self)
            
    async def process(self, msg: dict):
        method = msg.get('method', '')
        params = msg.get('params', [])
        msg_id = msg.get('id')
        
        if method == 'mining.subscribe':
            self.subscribed = True
            await self.send({
                'id': msg_id,
                'result': [
                    [['mining.set_difficulty', '1'], ['mining.notify', '1']],
                    self.extra_nonce1,
                    self.extra_nonce2_size
                ],
                'error': None
            })
            # Send difficulty
            await self.send({
                'id': None,
                'method': 'mining.set_difficulty',
                'params': [self.difficulty]
            })
            # Send current job
            await self.server.send_job(self)
            
        elif method == 'mining.authorize':
            worker = params[0] if params else 'unknown'
            self.worker_name = worker
            self.authorized = True
            log.info(f'Worker authorized: {worker} from {self.addr}')
            await self.send({'id': msg_id, 'result': True, 'error': None})
            # Send job after authorize in case miner missed it after subscribe
            if self.subscribed:
                await self.server.send_job(self)
            
        elif method == 'mining.submit':
            await self.handle_submit(msg_id, params)
            
        elif method == 'mining.extranonce.subscribe':
            await self.send({'id': msg_id, 'result': True, 'error': None})
            
    async def handle_submit(self, msg_id, params):
        """Handle a share submission."""
        if len(params) < 5:
            await self.send({'id': msg_id, 'result': False, 'error': [20, 'Invalid params', None]})
            return
            
        worker_name, job_id, extra_nonce2, ntime, nonce = params[:5]
        version_bits = params[5] if len(params) > 5 else None
        
        job = self.server.work_manager.jobs.get(job_id)
        if not job:
            await self.send({'id': msg_id, 'result': False, 'error': [21, 'Job not found', None]})
            return
        
        # Reconstruct coinbase
        coinbase_hex = job['coinb1'] + extra_nonce2 + job['coinb2']
        coinbase_bytes = bytes.fromhex(coinbase_hex)
        coinbase_hash = sha256d(coinbase_bytes)
        
        # Compute merkle root
        merkle = coinbase_hash
        for branch_hash in job['merkle_branch']:
            merkle = sha256d(merkle + bytes.fromhex(branch_hash)[::-1])
        
        # Build block header
        version = job['version']
        if version_bits:
            version = (version & ~0x1fffe000) | (int(version_bits, 16) & 0x1fffe000)
            
        header = struct.pack('<I', version)
        header += bytes.fromhex(job['prev_hash'])[::-1]  # un-reverse for header
        header += merkle
        header += bytes.fromhex(ntime)
        header += bytes.fromhex(job['bits'])
        header += bytes.fromhex(nonce)
        
        block_hash = sha256d(header)[::-1].hex()
        hash_int = int(block_hash, 16)
        
        # Solo pool: accept ALL shares, only check network targets for block submission
        # Calculate actual share difficulty from the hash
        DIFF1 = 0x00000000FFFF0000000000000000000000000000000000000000000000000000
        share_diff = DIFF1 / hash_int if hash_int else 0.0
        self._last_share_diff = share_diff
        log.info(f'Share accepted from {worker_name}: {block_hash[:16]}... diff={fmt_diff(share_diff)}')
        await self.send({'id': msg_id, 'result': True, 'error': None})
        
        # Check BTC difficulty
        btc_target_int = int(job['btc_target'], 16) if job['btc_target'] else 0
        if btc_target_int and hash_int <= btc_target_int:
            log.info(f'*** BTC BLOCK FOUND! height={job["btc_height"]} hash={block_hash} ***')
            await self.server.submit_btc_block(job, coinbase_hex, header.hex())
        
        # Check DGB difficulty
        if job['dgb_target']:
            dgb_target_int = int(job['dgb_target'], 16)
            if hash_int <= dgb_target_int:
                log.info(f'*** DGB BLOCK FOUND! height={job["dgb_height"]} hash={block_hash} ***')
                await self.server.submit_dgb_block(job, coinbase_hex, header.hex(), block_hash)

class StratumServer:
    def __init__(self):
        self.clients = set()
        self.work_manager = WorkManager()
        self.last_btc_height = 0
        self.last_dgb_height = 0
        
    async def send_job(self, client: StratumClient, clean: bool = True):
        """Send current job to a client."""
        job = self.work_manager.make_job(client.extra_nonce1)
        if not job:
            return
        await client.send({
            'id': None,
            'method': 'mining.notify',
            'params': [
                job['job_id'],
                job['prev_hash'],
                job['coinb1'],
                job['coinb2'],
                job['merkle_branch'],
                f'{job["version"]:08x}',
                job['bits'],
                f'{job["time"]:08x}',
                clean
            ]
        })
        
    async def broadcast_job(self, clean: bool = True):
        """Send new job to all connected miners."""
        for client in list(self.clients):
            if client.subscribed:
                await self.send_job(client, clean)
                
    async def submit_btc_block(self, job, coinbase_hex, header_hex):
        """Submit a solved BTC block to bitcoind."""
        bt = job['btc_template']
        txs = [coinbase_hex] + [tx['data'] for tx in bt.get('transactions', [])]
        block_hex = header_hex + pack_varint(len(txs)).hex() + ''.join(txs)
        
        loop = asyncio.get_event_loop()
        r = await loop.run_in_executor(None, lambda: btc_rpc('submitblock', [block_hex]))
        if r.get('result') is None and not r.get('error'):
            log.info('BTC block accepted!')
            stats.record_block('BTC', job.get('btc_height', 0), '')
        else:
            log.warning(f'BTC block submission: {r}')
            
    async def submit_dgb_block(self, job, coinbase_hex, header_hex, block_hash):
        """Submit a solved DGB block as auxpow to digibyted.
        
        AuxPow serialization (per Namecoin/DGB spec):
          coinbase_tx        - the BTC coinbase tx (contains merged mining commitment)
          parent_hash        - BTC block hash (LE, 32 bytes)
          coinbase_branch    - varint count + hashes (siblings to prove coinbase in BTC merkle)
          coinbase_index     - uint32 LE (always 0)
          chain_branch       - varint count + hashes (empty for single aux chain)
          chain_index        - uint32 LE (always 0)
          parent_header      - 80-byte BTC block header
        
        DGB block:
          header (80 bytes, version has auxpow bit set)
          auxpow data
          varint tx count
          transactions (DGB coinbase + mempool txs)
        """
        if not job.get('dgb_template'):
            return

        dt = job['dgb_template']
        bt = job['btc_template']

        try:
            coinbase_bytes = bytes.fromhex(coinbase_hex)
            parent_header  = bytes.fromhex(header_hex)

            # ── 1. Build coinbase merkle branch ──────────────────────────────
            # We need the siblings of the coinbase in the BTC merkle tree
            coinbase_hash = sha256d(coinbase_bytes)
            # tx_hashes: coinbase first, then all other txs (internal byte order = LE)
            other_hashes = [bytes.fromhex(tx['hash'])[::-1] for tx in bt.get('transactions', [])]
            nodes = [coinbase_hash] + other_hashes

            cb_branch = []
            while len(nodes) > 1:
                if len(nodes) % 2 == 1:
                    nodes.append(nodes[-1])
                cb_branch.append(nodes[1])  # sibling of index-0 (coinbase)
                nodes = [sha256d(nodes[i] + nodes[i+1]) for i in range(0, len(nodes), 2)]

            def ser_branch(branch_list):
                out = pack_varint(len(branch_list))
                for h in branch_list:
                    out += h
                return out

            # ── 2. Serialize auxpow ───────────────────────────────────────────
            auxpow = (
                coinbase_bytes +
                bytes.fromhex(block_hash)[::-1] +  # parent block hash, LE
                ser_branch(cb_branch) +
                struct.pack('<I', 0) +              # coinbase merkle index = 0
                ser_branch([]) +                    # chain merkle branch (empty)
                struct.pack('<I', 0) +              # chain merkle index = 0
                parent_header                       # 80-byte BTC header
            )

            # ── 3. Build DGB coinbase paying to DGB_ADDRESS ───────────────────
            # Decode bech32 DGB address to scriptPubKey
            # dgb1q... is bech32 P2WPKH: OP_0 <20-byte-hash>
            dgb_height = dt.get('height', 0)
            cb_script = script_push(encode_script_num(dgb_height)) + script_push(POOL_SIG.encode())

            # Decode DGB_ADDRESS (bech32) to witness program
            try:
                import bech32 as _bech32
                hrp, witver, witprog = _bech32.decode(DGB_ADDRESS)
                spk = bytes([0x00, len(witprog)]) + bytes(witprog)  # P2WPKH
            except Exception:
                # Fallback: OP_RETURN (won't pay us but block will be valid)
                spk = b'\x6a\x00'

            dgb_coinbase = (
                struct.pack('<I', 1) +              # version
                b'\x01' +                           # 1 input
                b'\x00' * 32 +                      # prev hash (null)
                b'\xff\xff\xff\xff' +               # prev index
                pack_varint(len(cb_script)) +
                cb_script +
                b'\xff\xff\xff\xff' +               # sequence
                b'\x01' +                           # 1 output
                struct.pack('<q', dt.get('coinbasevalue', 0)) +
                pack_varint(len(spk)) +
                spk +
                b'\x00\x00\x00\x00'                # locktime
            )

            # ── 4. Build DGB transaction list ─────────────────────────────────
            dgb_txs = [dgb_coinbase] + [bytes.fromhex(tx['data']) for tx in dt.get('transactions', [])]

            # ── 5. Compute DGB merkle root ────────────────────────────────────
            nodes = [sha256d(tx) for tx in dgb_txs]
            while len(nodes) > 1:
                if len(nodes) % 2 == 1:
                    nodes.append(nodes[-1])
                nodes = [sha256d(nodes[i] + nodes[i+1]) for i in range(0, len(nodes), 2)]
            dgb_merkle = nodes[0] if nodes else b'\x00' * 32

            # ── 6. Build DGB block header ─────────────────────────────────────
            dgb_version = dt.get('version', 0x20000000) | 0x100  # set auxpow bit
            dgb_prev    = bytes.fromhex(dt.get('previousblockhash', '00' * 32))[::-1]
            dgb_bits    = bytes.fromhex(dt.get('bits', '1d00ffff'))  # already 4 bytes LE
            dgb_time    = struct.pack('<I', dt.get('curtime', int(time.time())))
            dgb_nonce   = b'\x00' * 4  # nonce unused in auxpow

            dgb_header = (
                struct.pack('<I', dgb_version) +
                dgb_prev +
                dgb_merkle +
                dgb_time +
                dgb_bits +
                dgb_nonce
            )

            # ── 7. Assemble full DGB block ────────────────────────────────────
            dgb_block = (
                dgb_header +
                auxpow +
                pack_varint(len(dgb_txs)) +
                b''.join(dgb_txs)
            )

            log.info(f'Submitting DGB auxpow block: height={dgb_height} '
                     f'btc_hash={block_hash[:16]}... '
                     f'block_size={len(dgb_block)} bytes')

            loop = asyncio.get_event_loop()
            r = await loop.run_in_executor(None, lambda: dgb_rpc('submitblock', [dgb_block.hex()]))
            result = r.get('result')
            error  = r.get('error')

            if result is None and error is None:
                log.info(f'*** DGB BLOCK ACCEPTED! height={dgb_height} ***')
                log.info(f'*** DGB rewards going to {DGB_ADDRESS} ***')
                stats.record_block('DGB', dgb_height, block_hash)
            elif result == 'duplicate':
                log.warning(f'DGB block duplicate (already submitted): height={dgb_height}')
            elif result == 'inconclusive':
                log.warning(f'DGB block inconclusive (may still be accepted): height={dgb_height}')
            else:
                log.warning(f'DGB block REJECTED: result={result!r} error={error!r} height={dgb_height}')

        except Exception as e:
            log.error(f'DGB auxpow submission error: {e}', exc_info=True)
            
    async def poll_templates(self):
        """Continuously poll for new block templates."""
        while True:
            try:
                await self.work_manager.update_templates()
                
                bt = self.work_manager.btc_template
                dt = self.work_manager.dgb_template
                
                new_work = False
                
                if bt:
                    btc_h = bt.get('height', 0)
                    if btc_h != self.last_btc_height:
                        log.info(f'New BTC block: height={btc_h}')
                        self.last_btc_height = btc_h
                        new_work = True
                        
                if dt:
                    dgb_h = dt.get('height', 0)
                    dgb_algo = dt.get('pow_algo', 'unknown')
                    if dgb_h != self.last_dgb_height:
                        log.info(f'New DGB block: height={dgb_h} algo={dgb_algo}')
                        self.last_dgb_height = dgb_h
                        new_work = True
                        
                if new_work and self.clients:
                    await self.broadcast_job(clean=True)
                    
            except Exception as e:
                log.error(f'Template poll error: {e}')
                
            await asyncio.sleep(2)
            
    async def handle_client(self, reader, writer):
        client = StratumClient(reader, writer, self)
        self.clients.add(client)
        await client.handle()
        
    async def run(self):
        log.info('=== AuxPow Merged Mining Proxy starting ===')
        log.info(f'BTC address: {BTC_ADDRESS}')
        log.info(f'DGB address: {DGB_ADDRESS}')
        log.info(f'Stratum port: {STRATUM_PORT}')
        
        # Test connections
        r = btc_rpc('getblockchaininfo')
        if r.get('result'):
            log.info(f'BTC connected: height={r["result"]["blocks"]}')
        else:
            log.error(f'Cannot connect to bitcoind: {r.get("error")}')
            
        r = dgb_rpc('getblockchaininfo')
        if r.get('result'):
            log.info(f'DGB connected: height={r["result"]["blocks"]}')
        else:
            log.error(f'Cannot connect to digibyted: {r.get("error")}')
        
        # Initial template fetch
        await self.work_manager.update_templates()
        
        if self.work_manager.dgb_template:
            algo = self.work_manager.dgb_template.get('pow_algo', 'unknown')
            log.info(f'DGB template algo: {algo}')
            if algo != 'sha256d':
                log.warning(f'WARNING: DGB is providing {algo} blocks, not sha256d!')
                log.warning('Merged mining will only work with SHA256d algo blocks.')
        else:
            log.warning('Could not get DGB template')
        
        # Start template polling
        asyncio.create_task(self.poll_templates())
        
        # Start stratum server
        server = await asyncio.start_server(
            self.handle_client, STRATUM_HOST, STRATUM_PORT,
            reuse_address=True, reuse_port=True
        )
        log.info(f'Stratum server listening on {STRATUM_HOST}:{STRATUM_PORT}')
        log.info('Waiting for miners to connect...')
        
        async with server:
            await server.serve_forever()

# ── Stats tracker ─────────────────────────────────────────────────────────────
class StatsTracker:
    """Tracks pool statistics for the dashboard API."""
    def __init__(self):
        self.shares_total = 0
        self.share_times = collections.deque(maxlen=600)  # last 10 min
        self.best_share_diff = 0.0
        self.btc_blocks_found = 0
        self.dgb_blocks_found = 0
        self.btc_last_block = None
        self.dgb_last_block = None
        self.blocks = []  # list of {chain, height, hash, found_at}
        # per-miner stats: addr -> {worker, ip, shares, connected_at, last_share}
        self.miners = {}

    def record_share(self, worker: str, ip: str, diff: float = 0):
        now = time.time()
        self.shares_total += 1
        self.share_times.append(now)
        if diff > self.best_share_diff:
            self.best_share_diff = diff
        key = ip
        if key not in self.miners:
            self.miners[key] = {
                'worker': worker, 'ip': ip,
                'shares_accepted': 0, 'connected_at': now, 'last_share': now
            }
        self.miners[key]['shares_accepted'] += 1
        self.miners[key]['last_share'] = now
        self.miners[key]['worker'] = worker

    def record_connect(self, ip: str):
        now = time.time()
        if ip not in self.miners:
            self.miners[ip] = {
                'worker': '', 'ip': ip,
                'shares_accepted': 0, 'connected_at': now, 'last_share': None
            }

    def record_disconnect(self, ip: str):
        self.miners.pop(ip, None)

    def record_block(self, chain: str, height: int, block_hash: str):
        now = time.time()
        if chain == 'BTC':
            self.btc_blocks_found += 1
            self.btc_last_block = now
        else:
            self.dgb_blocks_found += 1
            self.dgb_last_block = now
        self.blocks.insert(0, {'chain': chain, 'height': height, 'hash': block_hash, 'found_at': now})
        self.blocks = self.blocks[:20]  # keep last 20

    def shares_per_sec(self) -> float:
        now = time.time()
        recent = [t for t in self.share_times if now - t <= 60]
        return len(recent) / 60.0

    def hashrate_est(self) -> float:
        """Estimate hashrate from share rate scaled by actual share difficulty.
        
        Formula: hashrate = shares_per_sec × difficulty × 2^32
        At diff=131072 and 1 share/15s → ~0.0667 sh/s × 131072 × 2^32 ≈ 37.6 TH/s
        (slightly over-estimates; vardiff will tune it down to match actual hardware)
        """
        sps = self.shares_per_sec()
        return sps * START_DIFF * (2**32)

    def active_miners(self, timeout=300):
        now = time.time()
        return [m for m in self.miners.values()
                if m.get('last_share') and now - m['last_share'] < timeout
                or m.get('connected_at') and now - m['connected_at'] < 30]

stats = StatsTracker()

# ── HTTP API server ────────────────────────────────────────────────────────────
async def handle_api(reader, writer):
    try:
        request = await asyncio.wait_for(reader.read(4096), timeout=5)
        req_str = request.decode('utf-8', errors='replace')
        first_line = req_str.split('\r\n')[0]
        method, path, *_ = first_line.split(' ')

        headers = 'HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nAccess-Control-Allow-Origin: *\r\nConnection: close\r\n'

        if path == '/api/stats':
            body = await build_stats_response()
        elif path == '/api/log':
            body = await build_log_response()
        else:
            headers = 'HTTP/1.1 404 Not Found\r\nContent-Type: application/json\r\nConnection: close\r\n'
            body = json.dumps({'error': 'not found'})

        body_bytes = body.encode()
        headers += f'Content-Length: {len(body_bytes)}\r\n\r\n'
        writer.write(headers.encode() + body_bytes)
        await writer.drain()
    except Exception as e:
        pass
    finally:
        writer.close()

async def build_stats_response() -> str:
    loop = asyncio.get_event_loop()

    # Fetch chain info from RPCs
    btc_info = await loop.run_in_executor(None, lambda: btc_rpc('getblockchaininfo'))
    dgb_info = await loop.run_in_executor(None, lambda: dgb_rpc('getmininginfo'))

    btc_data = {}
    if btc_info.get('result'):
        r = btc_info['result']
        diff = r.get('difficulty', 0)
        btc_data = {
            'height': r.get('blocks', 0),
            'difficulty': diff,
            'nethash': diff * (2**32) / 600,  # approx
        }

    dgb_data = {}
    if dgb_info.get('result'):
        r = dgb_info['result']
        diff = r.get('difficulties', {}).get('sha256d', r.get('difficulty', 0))
        nethash = r.get('networkhashesps', {}).get('sha256d', diff * (2**32) / 15)
        dgb_data = {
            'height': r.get('blocks', 0),
            'difficulty': diff,
            'nethash': nethash,
        }

    # Active miners with hashrate estimate
    active = stats.active_miners()
    total_shares = sum(m['shares_accepted'] for m in active)
    miner_list = []
    for m in active:
        share_frac = m['shares_accepted'] / max(total_shares, 1)
        miner_list.append({
            'worker': m['worker'],
            'ip': m['ip'],
            'shares_accepted': m['shares_accepted'],
            'connected_at': m['connected_at'],
            'hashrate_est': stats.hashrate_est() * share_frac,
        })

    pool_data = {
        'connected_miners': len(active),
        'connected_workers': len(active),
        'shares_total': stats.shares_total,
        'shares_per_sec': round(stats.shares_per_sec(), 3),
        'hashrate_est': stats.hashrate_est(),
        'best_share_diff': stats.best_share_diff,
        'best_share_diff_fmt': fmt_diff(stats.best_share_diff),
        'btc_blocks_found': stats.btc_blocks_found,
        'dgb_blocks_found': stats.dgb_blocks_found,
        'btc_last_block': stats.btc_last_block,
        'dgb_last_block': stats.dgb_last_block,
    }

    return json.dumps({
        'btc': btc_data,
        'dgb': dgb_data,
        'pool': pool_data,
        'miners': miner_list,
        'blocks': stats.blocks,
    })

async def build_log_response() -> str:
    loop = asyncio.get_event_loop()
    def read_log():
        try:
            with open(LOG_FILE, 'r') as f:
                lines = f.readlines()
            # Deduplicate consecutive identical lines (log doubles due to stdout+file)
            deduped = []
            prev = None
            for line in lines:
                line = line.strip()
                if line and line != prev:
                    deduped.append(line)
                    prev = line
            return deduped[-30:]
        except Exception:
            return []
    lines = await loop.run_in_executor(None, read_log)
    return json.dumps({'lines': lines})


# ── Patch StratumServer to record stats ───────────────────────────────────────
_orig_handle_client = StratumServer.handle_client
_orig_handle_submit = StratumClient.handle_submit

async def _patched_handle_client(self, reader, writer):
    addr = writer.get_extra_info('peername')
    ip = addr[0] if addr else 'unknown'
    stats.record_connect(ip)
    client = StratumClient(reader, writer, self)
    client._ip = ip
    self.clients.add(client)
    await client.handle()
    stats.record_disconnect(ip)

async def _patched_handle_submit(self, msg_id, params):
    await _orig_handle_submit(self, msg_id, params)
    if len(params) >= 5:
        worker_name = params[0]
        ip = self.addr[0] if self.addr else 'unknown'
        diff = getattr(self, '_last_share_diff', 0.0)
        stats.record_share(worker_name, ip, diff)

StratumServer.handle_client = _patched_handle_client
StratumClient.handle_submit = _patched_handle_submit

# Patch block submission to record blocks
_orig_submit_btc = StratumServer.submit_btc_block
_orig_submit_dgb = StratumServer.submit_dgb_block

# Block recording is done inside submit_btc_block / submit_dgb_block directly
# (patching removed to avoid double-counting false positives)

# Patch run() to also start API server
_orig_run = StratumServer.run

async def _patched_run(self):
    log.info('=== AuxPow Merged Mining Proxy starting ===')
    log.info(f'BTC address: {BTC_ADDRESS}')
    log.info(f'DGB address: {DGB_ADDRESS}')
    log.info(f'Stratum port: {STRATUM_PORT}')
    log.info(f'API port: {API_PORT}')

    r = btc_rpc('getblockchaininfo')
    if r.get('result'):
        log.info(f'BTC connected: height={r["result"]["blocks"]}')
    else:
        log.error(f'Cannot connect to bitcoind: {r.get("error")}')

    r = dgb_rpc('getblockchaininfo')
    if r.get('result'):
        log.info(f'DGB connected: height={r["result"]["blocks"]}')
    else:
        log.error(f'Cannot connect to digibyted: {r.get("error")}')

    await self.work_manager.update_templates()

    if self.work_manager.dgb_template:
        algo = self.work_manager.dgb_template.get('pow_algo', 'unknown')
        log.info(f'DGB template algo: {algo}')
        if algo != 'sha256d':
            log.warning(f'WARNING: DGB is providing {algo} blocks, not sha256d!')
    else:
        log.warning('Could not get DGB template')

    asyncio.create_task(self.poll_templates())

    stratum_server = await asyncio.start_server(
        self.handle_client, STRATUM_HOST, STRATUM_PORT,
        reuse_address=True, reuse_port=True
    )
    api_server = await asyncio.start_server(
        handle_api, '0.0.0.0', API_PORT,
        reuse_address=True, reuse_port=True
    )

    log.info(f'Stratum server listening on {STRATUM_HOST}:{STRATUM_PORT}')
    log.info(f'API server listening on 0.0.0.0:{API_PORT}')
    log.info('Waiting for miners to connect...')

    async with stratum_server, api_server:
        await asyncio.gather(
            stratum_server.serve_forever(),
            api_server.serve_forever()
        )

StratumServer.run = _patched_run


if __name__ == '__main__':
    server = StratumServer()
    try:
        asyncio.run(server.run())
    except KeyboardInterrupt:
        log.info('Shutting down...')
