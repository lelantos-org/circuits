// Emit asset_registry.json fixture consumed by contracts/script/Deploy.s.sol
// and contracts/test/MASP.deploy.t.sol. Generators come from the same
// HashToAssetGen used in-circuit (see Jubjub.hashToAssetGen below) so the
// registry the contract sees matches the prover's side.
import { writeFileSync, mkdirSync } from "fs";
import { dirname, resolve } from "path";
import { Jubjub } from "../test/helpers";

interface AssetSpec {
    id: number;
    symbol: string;
    name: string;
    decimals: number;
    scale: string;
}

const SPECS: AssetSpec[] = [
    { id: 1, symbol: "mUSDC", name: "Mock USDC", decimals: 6,  scale: "1" },
    { id: 2, symbol: "mDAI",  name: "Mock DAI",  decimals: 18, scale: "1" },
    { id: 3, symbol: "mWBTC", name: "Mock WBTC", decimals: 8,  scale: "1" },
];

async function main() {
    const J = await Jubjub.build();
    // Top-level parallel arrays — vm.parseJsonUintArray on Foundry doesn't
    // accept jsonpath wildcards (.assets[*].id), so pivot the data shape.
    const ids: string[] = [];
    const scales: string[] = [];
    const genXs: string[] = [];
    const genYs: string[] = [];
    const names: string[] = [];
    const symbols: string[] = [];
    const decimals: string[] = [];

    for (const s of SPECS) {
        const [x, y] = J.hashToAssetGen(BigInt(s.id));
        ids.push(s.id.toString());
        scales.push(s.scale);
        genXs.push(x.toString());
        genYs.push(y.toString());
        names.push(s.name);
        symbols.push(s.symbol);
        decimals.push(s.decimals.toString());
    }

    const outEnv = process.env.ASSET_REGISTRY_OUT;
    if (!outEnv) {
        throw new Error("ASSET_REGISTRY_OUT env var required (path to asset_registry.json)");
    }
    const out = resolve(outEnv);
    mkdirSync(dirname(out), { recursive: true });
    const payload = { ids, scales, genXs, genYs, names, symbols, decimals };
    writeFileSync(out, JSON.stringify(payload, null, 2) + "\n");
    console.log(`wrote ${ids.length} assets -> ${out}`);
}

main().catch(e => { console.error(e); process.exit(1); });
