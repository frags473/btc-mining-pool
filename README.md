# BTC + DGB AuxPoW Solo Mining Pool v1

A lightweight solo mining pool for **Bitcoin (BTC)** with **DigiByte (DGB) merged mining via AuxPoW**, running on a single Linux server.

## Architecture

```
Miner (Avalon / ASIC)
        │  Stratum (port 3032)
        ▼
  auxpow_proxy.py          ← Python asyncio Stratum server + AuxPoW bridge
        │
        ├──► bitcoind       ← Bitcoin Core full node (mainnet)  RPC :8332
        │
        └──► digibyted      ← DigiByte full node (mainnet, sha256d algo)  RPC :14022
```

- **Solo pool** — 100% of block rewards go directly to your configured addresses
- **AuxPoW merged mining** — every BTC share simultaneously attempts a DGB block
- **Stratum v1** compatible with all standard ASIC miners

## Quick Start

```bash
# 1. Copy and edit credentials
cp pool.conf.example pool.conf
chmod 600 pool.conf
nano pool.conf   # fill in your RPC credentials and wallet addresses

# 2. Deploy
cp auxpow_proxy.py ~/auxpow_proxy.py
sudo cp auxpow-proxy.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now auxpow-proxy

# 3. Point your miner
# stratum+tcp://YOUR_SERVER_IP:3032
# Username: YOUR_BTC_ADDRESS.worker1
# Password: x
```

## Files

| File | Description |
|------|-------------|
| `auxpow_proxy.py` | Main pool daemon |
| `pool.conf.example` | Credentials template — copy to `pool.conf` |
| `auxpow-proxy.service` | systemd service unit |
| `config/bitcoin.conf.example` | Bitcoin Core config template |
| `config/digibyte.conf.example` | DigiByte config template |
| `config/nginx-pool.conf` | nginx reverse proxy for dashboard |
| `dashboard/index.html` | Web dashboard |

> ⚠️ `pool.conf` is gitignored — it contains your passwords and wallet addresses and must never be committed.

## Ports

| Port | Purpose |
|------|---------|
| 3032 | Stratum mining |
| 8080 | Stats API (`/api/stats`) |
| 80   | Web dashboard (nginx) |

## License

MIT
