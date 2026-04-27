/* global snarkjs */
const $ = (id) => document.getElementById(id);
const log = (...a) => { const el = $("log"); el.textContent += a.join(" ") + "\n"; el.scrollTop = el.scrollHeight; };
const setStatus = (s, cls = "") => { const el = $("status"); el.textContent = s; el.className = cls; };

let inputJSON = null;

async function loadInput() {
    if (inputJSON) return inputJSON;
    const r = await fetch("/input.json");
    if (!r.ok) throw new Error("input.json fetch failed");
    inputJSON = await r.json();
    return inputJSON;
}

function stats(xs) {
    const s = [...xs].sort((a, b) => a - b);
    const mean = xs.reduce((a, b) => a + b, 0) / xs.length;
    const median = s[Math.floor(s.length / 2)];
    return { mean, median, min: s[0], max: s[s.length - 1] };
}

function deviceInfo() {
    return {
        ua: navigator.userAgent,
        platform: navigator.platform,
        cores: navigator.hardwareConcurrency || 0,
        memGB: navigator.deviceMemory || null,
        viewport: `${innerWidth}x${innerHeight}`,
    };
}

async function refreshTable() {
    const r = await fetch("/results");
    const rows = await r.json();
    const tb = $("tbl").querySelector("tbody");
    tb.innerHTML = "";
    for (const x of rows.slice().reverse()) {
        const tr = document.createElement("tr");
        const cells = [
            x.label || x.ua?.slice(0, 40) || "",
            x.cores ?? "",
            x.iters ?? "",
            x.meanMs?.toFixed?.(0) ?? "",
            x.medianMs?.toFixed?.(0) ?? "",
            x.minMs?.toFixed?.(0) ?? "",
            x.maxMs?.toFixed?.(0) ?? "",
            x.ts?.replace("T", " ").slice(0, 19) ?? "",
        ];
        for (const c of cells) {
            const td = document.createElement("td");
            td.textContent = String(c);
            tr.appendChild(td);
        }
        tb.appendChild(tr);
    }
}

async function run() {
    const iters = Math.max(1, Math.min(50, parseInt($("iters").value, 10) || 5));
    const label = $("label").value.trim();
    $("run").disabled = true;
    setStatus("loading…");
    try {
        log(`device: ${navigator.userAgent}`);
        log(`cores: ${navigator.hardwareConcurrency}, memGB: ${navigator.deviceMemory ?? "?"}`);

        const input = await loadInput();
        log("input.json loaded");

        const wasmURL = "/2x2.wasm";
        const zkeyURL = "/2x2_final.zkey";

        // Warm-up so the first proof's wasm/zkey download doesn't dominate.
        setStatus("warm-up…");
        const t0 = performance.now();
        await snarkjs.groth16.fullProve(input, wasmURL, zkeyURL);
        log(`warm-up: ${(performance.now() - t0).toFixed(0)} ms`);

        const times = [];
        for (let i = 0; i < iters; i++) {
            setStatus(`iter ${i + 1}/${iters}…`);
            const a = performance.now();
            await snarkjs.groth16.fullProve(input, wasmURL, zkeyURL);
            const dt = performance.now() - a;
            times.push(dt);
            log(`iter ${i + 1}: ${dt.toFixed(0)} ms`);
        }

        const s = stats(times);
        log(`mean=${s.mean.toFixed(0)} median=${s.median.toFixed(0)} min=${s.min.toFixed(0)} max=${s.max.toFixed(0)}`);

        const payload = {
            label,
            device: label || deviceInfo().platform,
            ...deviceInfo(),
            iters,
            timesMs: times,
            meanMs: s.mean,
            medianMs: s.median,
            minMs: s.min,
            maxMs: s.max,
        };
        const r = await fetch("/result", {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify(payload),
        });
        if (!r.ok) throw new Error("POST /result failed: " + r.status);
        setStatus("done", "ok");
        await refreshTable();
    } catch (e) {
        console.error(e);
        log("ERROR: " + (e.message || e));
        setStatus("error", "err");
    } finally {
        $("run").disabled = false;
    }
}

$("run").addEventListener("click", run);
refreshTable();
