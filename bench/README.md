# MASP 2x2 LAN Benchmark

Browser-side Groth16 proof bench. Server binds `0.0.0.0`; any device on the
same Wi-Fi opens the URL, runs `snarkjs.groth16.fullProve` locally, posts
timings back. Measures real per-device perf (phones, laptops, tablets).

## Prereqs

`build/2x2_js/2x2.wasm` and `build/2x2_final.zkey` must exist:

```
just compile
just setup
```

## Run

```
just bench-prepare   # one-time: build bench/public/input.json
just bench           # serve on :8787 (override with PORT=)
```

Server prints LAN URLs, e.g. `http://192.168.1.42:8787`. Open on each device,
set a label (`Pixel 8 Chrome`, `M2 MBP Safari`, …), click **Run benchmark**.

Per-device results appended to `bench/results.json` (JSONL).

## Notes

- Warm-up proof not counted (covers wasm/zkey download + JIT).
- `snarkjs.min.js` served from `node_modules` — no CDN, works offline.
- Firewall: macOS may prompt to accept incoming connections for `node`.
- zkey is 27 MB; first device load is bandwidth-bound, then browser-cached.
