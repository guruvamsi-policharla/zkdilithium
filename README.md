# Post-Quantum Anonymous Credentials [ePrint:2023/414](https://eprint.iacr.org/2023/414)

Rust implementation of the zkDilithium based anonymous credential scheme introduced in [ePrint:2023/414](https://eprint.iacr.org/2023/414)/

**WARNING:** This is an academic proof-of-concept prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.

## Dependencies
This project uses the [winterfell](https://github.com/facebook/winterfell/) crate as the backend for the STARK prover. We have a [fork](https://github.com/bwesterb/winterfell/) of this crate which contains the zkDilithium fields/extensions.

The [zkDilithium python spec](spec/zkdilithium.py) requires python 3.9 or below due to its dependence on the [Galois](https://github.com/mhostetter/galois) package.

## Overview
* [`spec/zkdilithium.py`](spec/zkdilithium.py): Python specification for the zkDilithium signature scheme. Can be run to generate a [testcase](spec/log/testcase.txt) that is plugged into the STARK prover.
* [`src/utils`](src/utils): Contains an implementation of the Poseidon hash function over the zkDilithium field and corresponding constraints.
* [`src/starkpf`](src/starkpf/): Contains the STARK prover which proves knowledge of a zkDilithium signature on a publicly known message m.

Run with 
```bash
cargo run --release
```

## License
This library is released under the MIT License.