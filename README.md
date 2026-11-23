# PGAP: post-quantum group authentication for RFID (NTRU-509 + Shamir)

Implementation and verification material for the paper on PGAP.

    PGAP-NTRU/
    ├── README.md
    ├── c/
    │   ├── pgap.c          C implementation and self-tests (NTRU-509, SHA-256, Shamir)
    │   └── results.txt     output of one run (23 checks, 0 failed)
    └── proverif/
        ├── pgap_A_honest.pv                 honest tag and server
        ├── pgap_B_compromised_tag.pv        one tag's private key leaked
        ├── pgap_C_unlinkability.pv          observational-equivalence test
        └── *_results.txt                    saved ProVerif output

## C implementation

Parameters: N = 509, p = 3, q = 2048, f in L(127,126), g, r in L(127,127),
n = 10 tags, k = 5, SHA-256, Shamir over the prime field 2^61 - 1.
Needs GCC with `__int128` and `/dev/urandom` (Linux, WSL, Docker).

    cd c
    gcc -O2 -Wall -Wextra -o pgap pgap.c
    ./pgap [y=127] [key_pairs=100] [sessions_per_pair=20]

Docker (PowerShell, from the `c` folder):

    docker run --rm -v "${PWD}:/src" -w /src gcc:13 sh -c "gcc -O2 -o /tmp/pgap pgap.c && /tmp/pgap"

Expected last line: `=== 23 checks, 0 failed ===`.
R1 SHA-256 vector, R2 NTRU keys, R3 Shamir, R4 single session, R5 group
authentication, R6 forged tag, R7 loss of M4/M5, R8 key agreement (2000
sessions), R9 protocol-level findings.

## ProVerif models

Tested with ProVerif 2.00 and later.

    cd proverif
    proverif pgap_A_honest.pv | grep RESULT
    proverif pgap_B_compromised_tag.pv | grep RESULT
    proverif pgap_C_unlinkability.pv | grep RESULT

| Model | Result |
|---|---|
| A: honest | secrecy of f, f_i, x_i, s(x_i), K holds; injective agreement for V1, V2, V3 holds |
| B: compromised tag | all secrecy and agreement queries fail (the tag recovers the server key f from M3) |
| C: unlinkability | equivalence cannot be proved (K, m2, V2 repeat across sessions) |

Model limits: NTRU is abstracted as ideal public-key encryption; the Shamir
threshold and the pseudonym update chain are not modelled (they are checked in
the C code); injective agreement is checked with one honest tag.

## Status

Research verification code only: not constant-time, not a production library.
