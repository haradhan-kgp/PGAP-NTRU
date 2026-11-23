# PGAP: C implementation with NTRU-509

C implementation and self-verification of PGAP (post-quantum group authentication
protocol for RFID: NTRU + Shamir secret sharing).

- NTRU-509: N = 509, p = 3, q = 2048, f in L(127,126), g, r in L(127,127)
- n = 10 tags, threshold k = 5, SHA-256, Shamir over the prime field 2^61 - 1
- Standard C only (needs GCC with `__int128` and `/dev/urandom`: Linux, WSL, Docker)

## Build and run

    gcc -O2 -Wall -Wextra -o pgap pgap.c
    ./pgap [y=127] [key_pairs=100] [sessions_per_pair=20]

Docker (PowerShell):

    docker run --rm -v "${PWD}:/src" -w /src gcc:13 sh -c "gcc -O2 -o /tmp/pgap pgap.c && /tmp/pgap"

Expected last line: `=== 23 checks, 0 failed ===`. Sample output is in `results.txt`.

## Checks (R1-R9)

R1 SHA-256 test vector, R2 NTRU keys, R3 Shamir, R4 single session, R5 group
authentication, R6 forged tag, R7 loss of M4/M5, R8 key agreement over 2000
sessions, R9 protocol-level findings (observations).

Verification harness only; not constant-time and not a production library.
