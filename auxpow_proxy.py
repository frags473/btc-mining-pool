#!/usr/bin/env python3

"""
BTC+DGB AuxPow Merged Mining Stratum Proxy
==========================================
Sits between miners and bitcoind's getblocktemplate.
- Fetches BTC block template from bitcoind
- Fetches DGB SHA256d block template from digibyted
- Embeds DGB auxpow commitment in BTC coinbase (merged mining)
- Serves miners via Stratum v1 on port 3032
- When a share meets DGB difficulty, submits AuxPoW block to digibyted
- When a share meets BTC difficulty, submits native block to bitcoind

MERGED MINING MODEL (AuxPoW):
  The miner hashes the BTC header. The BTC coinbase contains a commitment
  to the DGB block hash (fabe6d6d magic). When the BTC header hash meets
  the DGB target, we submit an AuxPoW block to digibyted:
    DGB block = DGB header (with auxpow version bit set) + AuxPoW data
  The AuxPoW data contains the BTC coinbase, BTC merkle branch, and BTC header.
  digibyted verifies: sha256d(btc_header) <= dgb_target.

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
import configparser as _cp
_cfg = _cp.ConfigParser()
_cfg_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pool.conf')
if not _cfg.read(_cfg_path):
    raise FileNotFoundError(f'pool.conf not found at {_cfg_path}')

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

MIN_DIFF   = 16384
START_DIFF = 32768
MAX_DIFF   = 131072

VARDIFF_TARGET_SECS  = 15
VARDIFF_RETARGET     = 90
VARDIFF_VARIANCE_PCT = 30

LOG_FILE = '/home/harry/auxpow_proxy.log'

# DGB AuxPoW version bit: version | 0x100 signals AuxPoW block
AUXPOW_VERSION_BIT = 0x100
# DGB chain ID for SHA256d = 1
DGB_CHAIN_ID = 1

# ── Logging ───────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format='[%(asctime)s] %(levelname)s %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S',
    handlers=[logging.StreamHandler(sys.stdout)]
)
log = logging.getLogger('auxpow')

# ── Crypto helpers ────────────────────────────────────────────────────────────
def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()

def bits_to_target(bits_hex: str) -> int:
    bits = int(bits_hex, 16)
    exp  = bits >> 24
    mant = bits & 0xFFFFFF
    return mant * (1 << (8 * (exp - 3)))

def target_to_diff(target: int) -> float:
    diff1 = 0x00000000FFFF0000000000000000000000000000000000000000000000000000
    return diff1 / target if target else 0

def diff_to_target(diff: float) -> int:
    diff1 = 0x00000000FFFF0000000000000000000000000000000000000000000000000000
    return int(diff1 / diff) if diff else 0

def fmt_diff(d: float) -> str:
    if d == 0:
        return '0'
    tiers = [
        (1e15, 'P'), (1e12, 'T'), (1e9, 'G'), (1e6, 'M'), (1e3, 'K'),
        (1.0, ''), (1e-3, 'm'), (1e-6, 'u'), (1e-9, 'n'),
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

# ── Bech32 decoder (no external dependency) ───────────────────────────────────
_BECH32_CHARSET = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l'

def bech32_decode_witprog(addr: str):
    """Decode a bech32 address. Returns (witver, witprog_bytes) or raises."""
    addr = addr.lower()
    pos = addr.rfind('1')
    if pos < 1:
        raise ValueError(f'Invalid bech32 address: {addr}')
    data5 = [_BECH32_CHARSET.find(c) for c in addr[pos+1:]]
    if any(x < 0 for x in data5):
        raise ValueError(f'Invalid bech32 character in: {addr}')
    # Strip 6-char checksum, convert 5-bit groups to 8-bit
    payload = data5[:-6]
    witver = payload[0]
    acc = 0
    bits = 0
    result = []
    for val in payload[1:]:
        acc = ((acc << 5) | val) & 0xffffffff
        bits += 5
        while bits >= 8:
            bits -= 8
            result.append((acc >> bits) & 0xff)
    return witver, bytes(result)

def addr_to_scriptpubkey(addr: str) -> bytes:
    """Convert a bech32 address to scriptPubKey bytes."""
    witver, witprog = bech32_decode_witprog(addr)
    # P2WPKH: OP_0 <20-byte-hash>  or  P2WSH: OP_0 <32-byte-hash>
    # OP_n for witver 0 = 0x00, witver 1+ = 0x51+witver-1
    op = 0x00 if witver == 0 else (0x50 + witver)
    return bytes([op, len(witprog)]) + witprog

# ── RPC ───────────────────────────────────────────────────────────────────────
def rpc(host, port, user, pw, method, params=None):
    if params is None:
        params = []
    payload = json.dumps({'jsonrpc': '1.0', 'id': 'p', 'method': method, 'params': params}).encode()
    creds = base64.b64encode(f'{user}:{pw}'.encode()).decode()
    req = urllib.request.Request(
        f'http://{host}:{port}/',
        data=payload,
        headers={'Content-Type': 'text/plain', 'Authorization': f'Basic {creds}'}
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

# ── AuxPoW commitment (goes in BTC coinbase input script) ─────────────────────
# Per Bitcoin merged mining spec (https://en.bitcoin.it/wiki/Merged_mining_specification):
#   magic:        fabe6d6d  (4 bytes) — "mm" in ASCII, doubled
#   chain_merkle: <32 bytes LE> — hash of the aux block header
#   merkle_size:  <4 bytes LE> — number of aux chains (1)
#   merkle_nonce: <4 bytes LE> — nonce (0)
MERGED_MAGIC = bytes.fromhex('fabe6d6d')

def build_auxpow_commitment(dgb_header_hash_hex: str) -> bytes:
    """
    Build the AuxPoW commitment to embed in the BTC coinbase.
    dgb_header_hash_hex: the DGB block header hash in display order (big-endian hex).
    The commitment stores it in little-endian (internal byte order).
    """
    # Display order (big-endian) -> internal (little-endian)
    dgb_hash_le = bytes.fromhex(dgb_header_hash_hex)[::-1]
    return (
        MERGED_MAGIC +
        dgb_hash_le +
        struct.pack('<I', 1) +   # merkle_size = 1
        struct.pack('<I', 0)     # merkle_nonce = 0
    )

def compute_dgb_header_hash(dt: dict) -> str:
    """
    Compute the hash of the DGB block header template (with nonce=0).
    This is what we commit to in the BTC coinbase.
    Returns display-order hex string.
    """
    dgb_version = dt.get('version', 0x20000000)
    dgb_prev    = bytes.fromhex(dt.get('previousblockhash', '00' * 32))[::-1]
    dgb_bits    = bytes.fromhex(dt.get('bits', '1d00ffff'))
    dgb_time    = struct.pack('<I', dt.get('curtime', int(time.time())))
    dgb_nonce   = b'\x00\x00\x00\x00'

    # We need a placeholder merkle root for the commitment hash
    # Use the coinbaseaux hash if available, otherwise zeros
    coinbaseaux = dt.get('coinbaseaux', {})
    if coinbaseaux:
        # Use first coinbaseaux value as placeholder
        merkle_placeholder = bytes.fromhex(list(coinbaseaux.values())[0])[::-1]
    else:
        merkle_placeholder = b'\x00' * 32

    dgb_header = (
        struct.pack('<I', dgb_version) +
        dgb_prev +
        merkle_placeholder +
        dgb_time +
        dgb_bits +
        dgb_nonce
    )
    return sha256d(dgb_header)[::-1].hex()

# ── Work manager ──────────────────────────────────────────────────────────────
class WorkManager:
    def __init__(self):
        self.btc_template = None
        self.dgb_template = None
        self.current_job_id = 0
        self.jobs = {}

    async def update_templates(self):
        """Fetch fresh templates from both daemons."""
        loop = asyncio.get_event_loop()

        btc = await loop.run_in_executor(None, lambda: btc_rpc('getblocktemplate', [{'rules': ['segwit']}]))
        if btc.get('result'):
            self.btc_template = btc['result']

        # DGB v8.26+ requires 'sha256d' as second positional argument
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
            err = dgb.get('error', {})
            import time as _time
            _now = _time.time()
            if not hasattr(self, '_dgb_err_last') or _now - self._dgb_err_last > 30:
                _msg = err.get('message', str(err)) if isinstance(err, dict) else str(err)
                log.warning(f'DGB not ready: {_msg} (will retry)')
                self._dgb_err_last = _now

    def make_job(self, extra_nonce1_hex: str) -> Optional[dict]:
        """
        Create a new mining job.

        MERGED MINING DESIGN:
        The miner hashes a BTC header. The BTC coinbase contains an AuxPoW
        commitment to the DGB block. When the BTC header hash meets the DGB
        target, we submit an AuxPoW block to digibyted.

        BTC coinbase structure:
          coinb1: version(4) + input_count(1) + null_prevhash(32) + previndex(4)
                  + script_len(varint) + height_script + pool_sig + auxpow_commitment
          [miner inserts: extra_nonce1(4) + extra_nonce2(8)]
          coinb2: sequence(4) + output_count(1) + value(8) + spk_len + spk
                  + witness_commitment_output(8+varint+38) + locktime(4)

        NOTE: extra_nonce1 is 4 bytes (os.urandom(4)), extra_nonce2_size is 8 bytes.
        Total extra nonce = 12 bytes.
        """
        if not self.btc_template:
            return None

        bt = self.btc_template
        self.current_job_id += 1
        job_id = f'{self.current_job_id:08x}'

        height = bt.get('height', 0)

        # ── Build AuxPoW commitment for DGB ──────────────────────────────────
        dgb_target = None
        dgb_height = None
        dgb_commitment = b''

        if self.dgb_template:
            dt = self.dgb_template
            dgb_height = dt.get('height', 0)
            dgb_bits_hex = dt.get('bits', '1d00ffff')
            dgb_target = f'{bits_to_target(dgb_bits_hex):064x}'

            # Compute the DGB block header hash to commit to
            dgb_hash_for_commitment = compute_dgb_header_hash(dt)
            dgb_commitment = build_auxpow_commitment(dgb_hash_for_commitment)
            log.debug(f"AuxPoW commitment: DGB height={dgb_height} hash={dgb_hash_for_commitment[:16]}...")

        # ── Build BTC coinbase ────────────────────────────────────────────────
        # extra_nonce1 = 4 bytes, extra_nonce2 = 8 bytes, total = 12 bytes
        extra_nonce1_bytes = bytes.fromhex(extra_nonce1_hex)  # 4 bytes
        extra_nonce2_size  = 8

        height_script = script_push(encode_script_num(height))
        sig_bytes     = POOL_SIG.encode('utf-8')
        script_prefix = height_script + script_push(sig_bytes) + dgb_commitment

        # Total script length = prefix + extra_nonce1(4) + extra_nonce2(8)
        script_total_len = len(script_prefix) + len(extra_nonce1_bytes) + extra_nonce2_size

        # coinb1: everything up to (but not including) extra_nonce1
        coinb1 = (
            '01000000' +                              # version LE
            '01' +                                    # input count
            '00' * 32 +                               # prev hash (null coinbase)
            'ffffffff' +                              # prev index
            pack_varint(script_total_len).hex() +     # script length (includes extra nonces)
            script_prefix.hex()
            # extra_nonce1 inserted by miner between coinb1 and coinb2
        )

        # ── Build coinb2 ─────────────────────────────────────────────────────
        # coinb2: sequence + outputs + locktime
        # BTC output: pay to BTC_ADDRESS
        btc_spk = addr_to_scriptpubkey(BTC_ADDRESS)
        coinbase_value = bt.get('coinbasevalue', 0)

        out_payment = (
            struct.pack('<q', coinbase_value) +
            pack_varint(len(btc_spk)) +
            btc_spk
        )

        # ── Witness commitment output (REQUIRED for segwit blocks) ────────────
        # BIP141: coinbase must have OP_RETURN output with witness commitment
        # witness_commitment = SHA256D(witness_merkle_root || witness_reserved_value)
        # witness_reserved_value = 32 zero bytes (goes in coinbase witness)
        # witness_merkle_root computed from wtxids of all transactions
        # coinbase wtxid = 0x00...00 (32 zeros)
        witness_reserved = bytes(32)

        # Compute witness merkle root from template wtxids
        # Template provides 'hash' field = wtxid for each tx
        wtxids = [bytes(32)]  # coinbase wtxid is all zeros
        for tx in bt.get('transactions', []):
            if 'hash' in tx:
                # 'hash' in getblocktemplate is the wtxid in display order
                wtxids.append(bytes.fromhex(tx['hash'])[::-1])
            else:
                # No witness data, use txid
                wtxids.append(bytes.fromhex(tx['txid'])[::-1])

        wnodes = list(wtxids)
        while len(wnodes) > 1:
            if len(wnodes) % 2 == 1:
                wnodes.append(wnodes[-1])
            wnodes = [sha256d(wnodes[i] + wnodes[i+1]) for i in range(0, len(wnodes), 2)]
        witness_merkle_root = wnodes[0]

        witness_commitment = sha256d(witness_merkle_root + witness_reserved)

        # OP_RETURN (0x6a) + push 36 bytes (0x24) + magic (aa21a9ed) + commitment (32 bytes)
        wc_script = bytes.fromhex('6a24aa21a9ed') + witness_commitment
        out_witness_commitment = (
            struct.pack('<q', 0) +           # value = 0
            pack_varint(len(wc_script)) +
            wc_script
        )

        # coinb2: sequence + 2 outputs + coinbase witness (for segwit marker) + locktime
        # NOTE: The coinbase tx uses segwit serialization:
        #   version(4) + marker(1=0x00) + flag(1=0x01) + inputs + outputs + witness + locktime
        # But stratum splits at extra_nonce boundary, so coinb1/coinb2 are non-witness parts.
        # The witness data (32 zero bytes) is appended after locktime in the full tx.
        # Actually for stratum, we send the non-witness serialization for the merkle txid,
        # but the full segwit serialization for submitblock.
        # We handle this in submit_btc_block by rebuilding the full segwit coinbase.

        coinb2 = (
            'ffffffff' +                              # sequence
            '02' +                                    # output count = 2
            out_payment.hex() +
            out_witness_commitment.hex() +
            '00000000'                                # locktime
        )

        # ── Previous block hash in stratum format ─────────────────────────────
        # ESP-Miner/NerdOctaXe stratum format:
        # stratum prevhash = reverse_words(internal_bytes)
        # where internal_bytes = display_bytes[::-1]
        prev_hash_display = bt.get('previousblockhash', '00' * 32)
        ph_internal = bytes.fromhex(prev_hash_display)[::-1]
        ph_stratum = b''
        for i in range(0, 32, 4):
            ph_stratum += ph_internal[i:i+4][::-1]
        prev_hash_stratum = ph_stratum.hex()

        # ── Merkle branch ─────────────────────────────────────────────────────
        txs = bt.get('transactions', [])
        tx_hashes = [tx['hash'] for tx in txs]
        merkle_branch = self._build_merkle_branch(tx_hashes)

        job = {
            'job_id':           job_id,
            'prev_hash':        prev_hash_stratum,
            'coinb1':           coinb1,
            'coinb2':           coinb2,
            'merkle_branch':    merkle_branch,
            'version':          bt.get('version', 0x20000000),
            'bits':             bt.get('bits', ''),
            'time':             bt.get('curtime', int(time.time())),
            'btc_target':       bt.get('target', ''),
            'btc_height':       height,
            'dgb_target':       dgb_target,
            'dgb_height':       dgb_height,
            'dgb_template':     self.dgb_template,
            'btc_template':     bt,
            'extra_nonce1':     extra_nonce1_hex,
            'extra_nonce2_size': extra_nonce2_size,
            'witness_reserved': witness_reserved.hex(),
        }

        self.jobs[job_id] = job

        # Prune old jobs to prevent memory leak (keep last 100)
        if len(self.jobs) > 100:
            oldest_keys = sorted(self.jobs.keys())[:-100]
            for k in oldest_keys:
                del self.jobs[k]

        return job

    def _build_merkle_branch(self, tx_hashes: List[str]) -> List[str]:
        """
        Build merkle branch for coinbase (position 0) in stratum format.

        tx_hashes: list of txid/wtxid hex strings in DISPLAY order (as from template).
        Full tx list is [coinbase, tx1, tx2, ...]. tx_hashes = [tx1, tx2, ...].

        Branch hashes are stored in INTERNAL byte order (little-endian).
        During share validation, coinbase_hash (sha256d output = internal order)
        is concatenated with branch hashes (also internal order). Consistent.
        """
        if not tx_hashes:
            return []
        # Convert display order to internal byte order
        nodes = [bytes.fromhex(h)[::-1] for h in tx_hashes]
        branch = []
        while nodes:
            # The sibling of the coinbase at this level is nodes[0]
            branch.append(nodes[0].hex())  # store in internal byte order
            if len(nodes) == 1:
                break
            remaining = nodes[1:]
            if len(remaining) % 2 == 1:
                remaining.append(remaining[-1])
            nodes = [sha256d(remaining[i] + remaining[i+1]) for i in range(0, len(remaining), 2)]
        return branch


# ── Stratum server ────────────────────────────────────────────────────────────
class StratumClient:
    def __init__(self, reader, writer, server):
        self.reader = reader
        self.writer = writer
        self.server = server
        self.extra_nonce1 = os.urandom(4).hex()   # 4 bytes
        self.extra_nonce2_size = 8
        self.subscribed = False
        self.authorized = False
        self.worker_name = ''
        self.difficulty = START_DIFF
        self.addr = writer.get_extra_info('peername')
        self._last_share_diff = 0.0
        # VarDiff state
        self._share_times = collections.deque()
        self._last_retarget = time.time()

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
            await self.send({
                'id': None,
                'method': 'mining.set_difficulty',
                'params': [self.difficulty]
            })
            await self.server.send_job(self)

        elif method == 'mining.authorize':
            worker = params[0] if params else 'unknown'
            self.worker_name = worker
            self.authorized = True
            log.info(f'Worker authorized: {worker} from {self.addr}')
            await self.send({'id': msg_id, 'result': True, 'error': None})
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

        # ── Reconstruct coinbase (non-witness, for merkle txid) ───────────────
        # coinb1 + extra_nonce1(4 bytes) + extra_nonce2(8 bytes) + coinb2
        coinbase_hex = job['coinb1'] + job['extra_nonce1'] + extra_nonce2 + job['coinb2']
        coinbase_bytes = bytes.fromhex(coinbase_hex)
        # txid = sha256d of non-witness serialization
        coinbase_hash = sha256d(coinbase_bytes)  # internal byte order

        # ── Compute merkle root ───────────────────────────────────────────────
        # Branch hashes are in internal byte order (consistent with coinbase_hash)
        merkle = coinbase_hash
        for branch_hash in job['merkle_branch']:
            merkle = sha256d(merkle + bytes.fromhex(branch_hash))

        # ── Build block header ────────────────────────────────────────────────
        version = job['version']
        if version_bits:
            version = (version & ~0x1fffe000) | (int(version_bits, 16) & 0x1fffe000)

        # Reconstruct prev_hash for header from stratum format:
        # stratum = reverse_words(internal), so header = reverse_words(stratum)
        ph_bytes = bytes.fromhex(job['prev_hash'])
        ph_header = b''
        for i in range(0, 32, 4):
            ph_header += ph_bytes[i:i+4][::-1]

        # ntime and nonce from stratum are big-endian hex strings
        # Bitcoin header fields are little-endian
        ntime_bytes = bytes.fromhex(ntime)[::-1]   # BE hex -> LE bytes
        nonce_bytes = bytes.fromhex(nonce)[::-1]   # BE hex -> LE bytes
        bits_bytes  = bytes.fromhex(job['bits'])[::-1]  # bits from template is BE hex

        header = (
            struct.pack('<I', version) +
            ph_header +
            merkle +
            ntime_bytes +
            bits_bytes +
            nonce_bytes
        )
        assert len(header) == 80

        block_hash = sha256d(header)[::-1].hex()
        hash_int   = int(block_hash, 16)

        # ── Accept share ──────────────────────────────────────────────────────
        DIFF1 = 0x00000000FFFF0000000000000000000000000000000000000000000000000000
        share_diff = DIFF1 / hash_int if hash_int else 0.0
        self._last_share_diff = share_diff
        log.info(f'Share accepted from {worker_name}: {block_hash[:16]}... diff={fmt_diff(share_diff)}')
        stats.record_share(worker_name, getattr(self, '_ip', 'unknown'), share_diff)
        await self.send({'id': msg_id, 'result': True, 'error': None})

        # ── VarDiff ───────────────────────────────────────────────────────────
        now = time.time()
        self._share_times.append(now)
        # Remove shares older than retarget window
        while self._share_times and now - self._share_times[0] > VARDIFF_RETARGET:
            self._share_times.popleft()
        if now - self._last_retarget >= VARDIFF_RETARGET and len(self._share_times) >= 2:
            elapsed = self._share_times[-1] - self._share_times[0]
            n_shares = len(self._share_times) - 1
            actual_secs = elapsed / n_shares if n_shares > 0 else VARDIFF_TARGET_SECS
            ratio = actual_secs / VARDIFF_TARGET_SECS
            variance = abs(ratio - 1.0)
            if variance > VARDIFF_VARIANCE_PCT / 100.0:
                new_diff = int(self.difficulty * ratio)
                new_diff = max(MIN_DIFF, min(MAX_DIFF, new_diff))
                if new_diff != self.difficulty:
                    self.difficulty = new_diff
                    log.info(f'VarDiff {worker_name}: {fmt_diff(self.difficulty)} (actual={actual_secs:.1f}s target={VARDIFF_TARGET_SECS}s)')
                    await self.send({
                        'id': None,
                        'method': 'mining.set_difficulty',
                        'params': [self.difficulty]
                    })
            self._last_retarget = now

        # ── Check BTC target ──────────────────────────────────────────────────
        btc_target_int = int(job['btc_target'], 16) if job['btc_target'] else 0
        if btc_target_int and hash_int <= btc_target_int:
            log.info(f'*** BTC BLOCK FOUND! height={job["btc_height"]} hash={block_hash} ***')
            await self.server.submit_btc_block(job, coinbase_hex, header.hex(), extra_nonce2)

        # ── Check DGB target (AuxPoW merged mining) ───────────────────────────
        if job['dgb_target']:
            dgb_target_int = int(job['dgb_target'], 16)
            log.info(f'DGB check: hash={block_hash[:16]}... hash_int={hash_int:#066x} dgb_target={dgb_target_int:#066x} meets_dgb={hash_int <= dgb_target_int}')
            if hash_int <= dgb_target_int:
                log.info(f'*** DGB BLOCK FOUND! height={job["dgb_height"]} hash={block_hash} ***')
                await self.server.submit_dgb_auxpow_block(job, coinbase_hex, header.hex(), block_hash, extra_nonce2)


class StratumServer:
    def __init__(self):
        self.clients = set()
        self.work_manager = WorkManager()
        self.last_btc_height = 0
        self.last_dgb_height = 0

    async def send_job(self, client: StratumClient, clean: bool = True):
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
        for client in list(self.clients):
            if client.subscribed:
                await self.send_job(client, clean)

    async def submit_btc_block(self, job, coinbase_hex_nowit, header_hex, extra_nonce2):
        """
        Submit a solved BTC block to bitcoind.

        The coinbase_hex_nowit is the non-witness serialization (used for merkle txid).
        For submitblock we need the full segwit serialization with witness data.
        """
        bt = job['btc_template']

        # Rebuild full segwit coinbase from parts
        # coinb1 + extra_nonce1 + extra_nonce2 + coinb2 = non-witness coinbase
        # We need to insert segwit marker/flag and witness field
        coinb1_bytes = bytes.fromhex(job['coinb1'])
        en1_bytes    = bytes.fromhex(job['extra_nonce1'])
        en2_bytes    = bytes.fromhex(extra_nonce2)
        coinb2_bytes = bytes.fromhex(job['coinb2'])

        # Non-witness coinbase: version(4) + input_count(1) + input + output_count(1) + outputs + locktime(4)
        # Segwit coinbase:      version(4) + 0x00 0x01 + input_count(1) + input + output_count(1) + outputs + witness + locktime(4)
        # The witness for the coinbase input is the witness_reserved value (32 zero bytes)
        # We insert marker+flag after version (first 4 bytes of coinb1)

        nowit_full = coinb1_bytes + en1_bytes + en2_bytes + coinb2_bytes

        # version is first 4 bytes
        version_bytes = nowit_full[:4]
        rest = nowit_full[4:]  # input_count + input + output_count + outputs + locktime

        # Strip locktime (last 4 bytes) to insert witness before it
        rest_no_locktime = rest[:-4]
        locktime_bytes   = rest[-4:]

        # Witness for coinbase input: 1 item, 32 zero bytes
        witness_reserved = bytes.fromhex(job['witness_reserved'])
        witness_field = (
            b'\x01' +                          # 1 witness item
            pack_varint(len(witness_reserved)) +
            witness_reserved
        )

        segwit_coinbase = (
            version_bytes +
            b'\x00\x01' +                      # segwit marker + flag
            rest_no_locktime +
            witness_field +
            locktime_bytes
        )

        txs = [segwit_coinbase.hex()] + [tx['data'] for tx in bt.get('transactions', [])]
        block_hex = header_hex + pack_varint(len(txs)).hex() + ''.join(txs)

        loop = asyncio.get_event_loop()
        r = await loop.run_in_executor(None, lambda: btc_rpc('submitblock', [block_hex]))
        result = r.get('result')
        error  = r.get('error')
        if result is None and error is None:
            log.info(f'*** BTC BLOCK ACCEPTED! height={job["btc_height"]} ***')
            log.info(f'*** BTC rewards going to {BTC_ADDRESS} ***')
            stats.record_block('BTC', job.get('btc_height', 0), '')
        else:
            log.warning(f'BTC block submission: result={result!r} error={error!r}')

    async def submit_dgb_auxpow_block(self, job, coinbase_hex_nowit, btc_header_hex, btc_block_hash, extra_nonce2):
        """
        Submit a solved DGB block to digibyted using AuxPoW.

        AUXPOW MERGED MINING:
        The miner hashed the BTC header and its sha256d hash meets the DGB target.
        We submit to digibyted an AuxPoW block:

          DGB block = DGB_header + AuxPoW_data + DGB_tx_count + DGB_transactions

        DGB_header (80 bytes):
          version (with AUXPOW_VERSION_BIT set) + dgb_prevhash + dgb_merkle_root
          + dgb_time + dgb_bits + dgb_nonce (all zeros, not used for PoW)

        AuxPoW_data:
          coinbase_tx:      the BTC coinbase transaction (full, with witness)
          coinbase_branch:  merkle branch from BTC coinbase to BTC merkle root
          chain_merkle:     merkle branch for aux chain (empty, only 1 chain)
          parent_block:     the BTC block header (80 bytes)

        digibyted verifies:
          1. sha256d(parent_block) <= dgb_target
          2. BTC coinbase contains fabe6d6d commitment to DGB block hash
          3. DGB block hash matches commitment
        """
        if not job.get('dgb_template'):
            log.error('DGB template missing for AuxPoW submission')
            return

        dt = job['dgb_template']
        dgb_height = dt.get('height', 0)

        try:
            # ── Build BTC coinbase (segwit, same as submit_btc_block) ─────────
            coinb1_bytes = bytes.fromhex(job['coinb1'])
            en1_bytes    = bytes.fromhex(job['extra_nonce1'])
            en2_bytes    = bytes.fromhex(extra_nonce2)
            coinb2_bytes = bytes.fromhex(job['coinb2'])

            nowit_full = coinb1_bytes + en1_bytes + en2_bytes + coinb2_bytes
            version_bytes        = nowit_full[:4]
            rest                 = nowit_full[4:]
            rest_no_locktime     = rest[:-4]
            locktime_bytes       = rest[-4:]
            witness_reserved     = bytes.fromhex(job['witness_reserved'])
            witness_field = (
                b'\x01' +
                pack_varint(len(witness_reserved)) +
                witness_reserved
            )
            btc_coinbase_tx = (
                version_bytes +
                b'\x00\x01' +
                rest_no_locktime +
                witness_field +
                locktime_bytes
            )

            # ── Build BTC coinbase merkle branch ──────────────────────────────
            # This is the branch from the BTC coinbase txid to the BTC merkle root.
            # job['merkle_branch'] contains the branch hashes in internal byte order.
            # AuxPoW serialization: each hash is 32 bytes LE (internal order).
            btc_merkle_branch_hashes = [bytes.fromhex(h) for h in job['merkle_branch']]

            # ── Build DGB coinbase transaction ────────────────────────────────
            dgb_cb_script = script_push(encode_script_num(dgb_height)) + script_push(POOL_SIG.encode())
            dgb_spk = addr_to_scriptpubkey(DGB_ADDRESS)

            dgb_coinbase = (
                struct.pack('<I', 1) +           # version
                b'\x01' +                        # input count
                b'\x00' * 32 +                   # prev hash (null)
                b'\xff\xff\xff\xff' +             # prev index
                pack_varint(len(dgb_cb_script)) +
                dgb_cb_script +
                b'\xff\xff\xff\xff' +             # sequence
                b'\x01' +                        # output count
                struct.pack('<q', dt.get('coinbasevalue', 0)) +
                pack_varint(len(dgb_spk)) +
                dgb_spk +
                b'\x00\x00\x00\x00'              # locktime
            )

            # ── Build DGB transaction list ────────────────────────────────────
            dgb_txs = [dgb_coinbase] + [bytes.fromhex(tx['data']) for tx in dt.get('transactions', [])]

            # ── Compute DGB merkle root ───────────────────────────────────────
            nodes = [sha256d(tx) for tx in dgb_txs]
            while len(nodes) > 1:
                if len(nodes) % 2 == 1:
                    nodes.append(nodes[-1])
                nodes = [sha256d(nodes[i] + nodes[i+1]) for i in range(0, len(nodes), 2)]
            dgb_merkle = nodes[0]  # internal byte order

            # ── Build DGB header ──────────────────────────────────────────────
            # Version MUST have AUXPOW_VERSION_BIT set (0x100) to signal AuxPoW
            dgb_version_base = dt.get('version', 0x20000000)
            dgb_version      = dgb_version_base | AUXPOW_VERSION_BIT
            dgb_prev         = bytes.fromhex(dt.get('previousblockhash', '00' * 32))[::-1]
            dgb_bits         = bytes.fromhex(dt.get('bits', '1d00ffff'))
            dgb_time         = struct.pack('<I', dt.get('curtime', int(time.time())))
            dgb_nonce        = b'\x00\x00\x00\x00'  # not used for PoW in AuxPoW

            dgb_header = (
                struct.pack('<I', dgb_version) +
                dgb_prev +
                dgb_merkle +
                dgb_time +
                dgb_bits +
                dgb_nonce
            )
            assert len(dgb_header) == 80

            # ── Serialize AuxPoW data ─────────────────────────────────────────
            # Per https://en.bitcoin.it/wiki/Merged_mining_specification
            # AuxPoW structure:
            #   coinbase_tx:          <varint len> <tx bytes>  (the BTC coinbase)
            #   coinbase_branch:      <varint count> <hash1> ... <branch_side_mask(4 bytes LE)>
            #   chain_merkle_branch:  <varint count=0> <branch_side_mask(4 bytes LE)>
            #   parent_block:         <80 bytes BTC header>

            # Coinbase tx (length-prefixed)
            auxpow_coinbase = (
                pack_varint(len(btc_coinbase_tx)) +
                btc_coinbase_tx
            )

            # Coinbase merkle branch (branch from coinbase to BTC merkle root)
            auxpow_cb_branch = pack_varint(len(btc_merkle_branch_hashes))
            for h in btc_merkle_branch_hashes:
                auxpow_cb_branch += h  # already internal byte order (32 bytes LE)
            auxpow_cb_branch += struct.pack('<I', 0)  # branch_side_mask = 0 (coinbase is always left)

            # Chain merkle branch (empty — only 1 aux chain)
            auxpow_chain_branch = (
                pack_varint(0) +             # 0 hashes
                struct.pack('<I', 0)         # branch_side_mask = 0
            )

            # Parent block header (the BTC header)
            btc_header_bytes = bytes.fromhex(btc_header_hex)
            assert len(btc_header_bytes) == 80

            auxpow_data = (
                auxpow_coinbase +
                auxpow_cb_branch +
                auxpow_chain_branch +
                btc_header_bytes
            )

            # ── Assemble full DGB AuxPoW block ────────────────────────────────
            dgb_block = (
                dgb_header +
                auxpow_data +
                pack_varint(len(dgb_txs)) +
                b''.join(dgb_txs)
            )

            # Verify BTC hash meets DGB target
            btc_hash = sha256d(btc_header_bytes)[::-1].hex()
            btc_hash_int = int(btc_hash, 16)
            dgb_target_int = bits_to_target(dt.get('bits', '1d00ffff'))
            log.info(f'AuxPoW: BTC hash={btc_hash[:16]}... meets_dgb_target={btc_hash_int <= dgb_target_int}')
            log.info(f'Submitting DGB AuxPoW block: height={dgb_height} block_size={len(dgb_block)} bytes txs={len(dgb_txs)}')

            loop = asyncio.get_event_loop()
            r = await loop.run_in_executor(None, lambda: dgb_rpc('submitblock', [dgb_block.hex()]))
            result = r.get('result')
            error  = r.get('error')

            if result is None and error is None:
                log.info(f'*** DGB BLOCK ACCEPTED! height={dgb_height} ***')
                log.info(f'*** DGB rewards going to {DGB_ADDRESS} ***')
                stats.record_block('DGB', dgb_height, btc_block_hash)
            elif result == 'duplicate':
                log.warning(f'DGB block duplicate: height={dgb_height}')
            elif result == 'inconclusive':
                log.warning(f'DGB block inconclusive: height={dgb_height}')
            else:
                log.warning(f'DGB block REJECTED: result={result!r} error={error!r} height={dgb_height}')

        except Exception as e:
            log.error(f'DGB AuxPoW submission error: {e}', exc_info=True)

    async def poll_templates(self):
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
                    dgb_h    = dt.get('height', 0)
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
        addr = writer.get_extra_info('peername')
        ip = addr[0] if addr else 'unknown'
        stats.record_connect(ip)
        client = StratumClient(reader, writer, self)
        client._ip = ip
        self.clients.add(client)
        await client.handle()
        stats.record_disconnect(ip)

    async def run(self):
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
            log.warning('Could not get DGB template on startup (will retry)')

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


# ── Stats tracker ─────────────────────────────────────────────────────────────
class StatsTracker:
    def __init__(self):
        self.shares_total    = 0
        self.share_times     = collections.deque(maxlen=600)
        self.best_share_diff = 0.0
        self.btc_blocks_found = 0
        self.dgb_blocks_found = 0
        self.btc_last_block  = None
        self.dgb_last_block  = None
        self.blocks          = []
        self.miners          = {}

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
        # Keep miner data so share history persists across reconnects
        if ip in self.miners:
            self.miners[ip]['disconnected_at'] = time.time()

    def record_block(self, chain: str, height: int, block_hash: str):
        now = time.time()
        if chain == 'BTC':
            self.btc_blocks_found += 1
            self.btc_last_block = now
        else:
            self.dgb_blocks_found += 1
            self.dgb_last_block = now
        self.blocks.insert(0, {'chain': chain, 'height': height, 'hash': block_hash, 'found_at': now})
        self.blocks = self.blocks[:20]

    def shares_per_sec(self) -> float:
        now = time.time()
        recent = [t for t in self.share_times if now - t <= 60]
        return len(recent) / 60.0

    def hashrate_est(self) -> float:
        sps = self.shares_per_sec()
        return sps * START_DIFF * (2 ** 32)

    def active_miners(self, timeout=300):
        now = time.time()
        return [m for m in self.miners.values()
                if (m.get('last_share') and now - m['last_share'] < timeout)
                or (m.get('connected_at') and now - m['connected_at'] < 120)]


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
    except Exception:
        pass
    finally:
        writer.close()


async def build_stats_response() -> str:
    loop = asyncio.get_event_loop()
    btc_info = await loop.run_in_executor(None, lambda: btc_rpc('getblockchaininfo'))
    dgb_info = await loop.run_in_executor(None, lambda: dgb_rpc('getmininginfo'))

    btc_data = {}
    if btc_info.get('result'):
        r = btc_info['result']
        diff = r.get('difficulty', 0)
        btc_data = {
            'height':     r.get('blocks', 0),
            'difficulty': diff,
            'nethash':    diff * (2 ** 32) / 600,
        }

    dgb_data = {}
    if dgb_info.get('result'):
        r = dgb_info['result']
        diff = r.get('difficulties', {}).get('sha256d', r.get('difficulty', 0))
        nethash = r.get('networkhashesps', {}).get('sha256d', diff * (2 ** 32) / 15)
        dgb_data = {
            'height':     r.get('blocks', 0),
            'difficulty': diff,
            'nethash':    nethash,
        }

    active = stats.active_miners()
    total_shares = sum(m['shares_accepted'] for m in active)
    miner_list = []
    for m in active:
        share_frac = m['shares_accepted'] / max(total_shares, 1)
        miner_list.append({
            'worker':           m['worker'],
            'ip':               m['ip'],
            'shares_accepted':  m['shares_accepted'],
            'connected_at':     m['connected_at'],
            'hashrate_est':     stats.hashrate_est() * share_frac,
        })

    pool_data = {
        'connected_miners':    len(active),
        'connected_workers':   len(miner_list),
        'shares_total':        stats.shares_total,
        'shares_per_sec':      round(stats.shares_per_sec(), 3),
        'hashrate_est':        stats.hashrate_est(),
        'best_share_diff':     stats.best_share_diff,
        'best_share_diff_fmt': fmt_diff(stats.best_share_diff),
        'btc_blocks_found':    stats.btc_blocks_found,
        'dgb_blocks_found':    stats.dgb_blocks_found,
        'btc_last_block':      stats.btc_last_block,
        'dgb_last_block':      stats.dgb_last_block,
    }

    return json.dumps({
        'btc':    btc_data,
        'dgb':    dgb_data,
        'pool':   pool_data,
        'miners': miner_list,
        'blocks': stats.blocks,
    })


async def build_log_response() -> str:
    loop = asyncio.get_event_loop()
    def read_log():
        try:
            with open(LOG_FILE, 'r') as f:
                lines = f.readlines()
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


if __name__ == '__main__':
    server = StratumServer()
    try:
        asyncio.run(server.run())
    except KeyboardInterrupt:
        log.info('Shutting down...')
