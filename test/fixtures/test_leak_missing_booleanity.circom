pragma circom 2.2.3;

// Deliberately broken. Negative control for the booleanity check in
// `test/lib/bit_groups.ts`; not part of any circuit under `src/`.
//
// A decomposition that constrains every digit to {0, 1} except index `FREE`.
// That digit is a free field element, so the weighted sum reaches any target
// and the decomposition range-checks nothing.
template LeakMissingBooleanity(n, FREE) {
    signal input in;
    signal output bits[n];

    var lc = 0;
    var e = 1;
    for (var i = 0; i < n; i++) {
        bits[i] <-- (in >> i) & 1;
        if (i != FREE) {
            bits[i] * (bits[i] - 1) === 0;
        }
        lc += bits[i] * e;
        e = e + e;
    }
    lc === in;
}

component main { public [ in ] } = LeakMissingBooleanity(16, 5);
