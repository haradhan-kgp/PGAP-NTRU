/*
 * pgap.c -- C implementation and self-verification of PGAP
 *           (Post-quantum Group Authentication Protocol, NTRU + Shamir)
 *
 * NTRU parameters (NTRU-509, as in the paper):  N = 509, p = 3, q = 2048
 * Sampling sets: f in L(y, y-1), g, r in L(y, y)   (default y = 127, i.e.
 *                254 non-zero coefficients, same density as NTRU-HPS-2048-509)
 *
 * Build:  gcc -O2 -Wall -Wextra -o pgap pgap.c
 * Run:    ./pgap [y=127] [key_pairs=100] [sessions_per_pair=20]
 *
 * Nothing here is constant-time; this is a protocol-verification harness,
 * not a production library.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>

#define N      509
#define P      3
#define Q      2048
#define QMASK  (Q - 1)
#define NTAGS  10               /* n : number of tags            */
#define KTHR   5                /* k : Shamir threshold          */

static int g_y = 127;               /* weight parameter y of L(y,y)         */
static int g_maxabs = 0;            /* max |coeff| of f*e mod q seen        */
static long g_checks = 0, g_fail = 0;
static int  g_trace = 0;            /* print a one-line status per session */


#define OKMSG(cond, ...) do { int _c = !!(cond); g_checks++; if (!_c) g_fail++; \
    printf("  [%s] ", _c ? "ok" : "FAIL"); printf(__VA_ARGS__); printf("\n"); } while (0)

/* ------------------------------------------------------------------ RNG */
static uint32_t rnd32(void) {
    static uint8_t buf[4096];
    static size_t pos = sizeof buf;
    if (pos >= sizeof buf) {
        FILE *f = fopen("/dev/urandom", "rb");
        if (!f || fread(buf, 1, sizeof buf, f) != sizeof buf) { perror("urandom"); exit(1); }
        fclose(f);
        pos = 0;
    }
    uint32_t v; memcpy(&v, buf + pos, 4); pos += 4; return v;
}
static uint32_t rnd_below(uint32_t n) {
    uint32_t lim = UINT32_MAX - (UINT32_MAX % n), v;
    do v = rnd32(); while (v >= lim);
    return v % n;
}
static uint64_t rnd64(void) { return ((uint64_t)rnd32() << 32) | rnd32(); }

/* --------------------------------------------------------------- SHA-256 */
typedef struct { uint32_t h[8]; uint8_t b[64]; uint64_t len; size_t n; } sha_t;
static const uint32_t K256[64] = {
0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
#define ROR(x,n) (((x) >> (n)) | ((x) << (32 - (n))))
static void sha_block(sha_t *s, const uint8_t *p) {
    uint32_t w[64], a, b, c, d, e, f, g, h, t1, t2;
    for (int i = 0; i < 16; i++)
        w[i] = (uint32_t)p[4*i] << 24 | p[4*i+1] << 16 | p[4*i+2] << 8 | p[4*i+3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = ROR(w[i-15],7) ^ ROR(w[i-15],18) ^ (w[i-15] >> 3);
        uint32_t s1 = ROR(w[i-2],17) ^ ROR(w[i-2],19) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    a=s->h[0]; b=s->h[1]; c=s->h[2]; d=s->h[3]; e=s->h[4]; f=s->h[5]; g=s->h[6]; h=s->h[7];
    for (int i = 0; i < 64; i++) {
        t1 = h + (ROR(e,6)^ROR(e,11)^ROR(e,25)) + ((e&f)^(~e&g)) + K256[i] + w[i];
        t2 = (ROR(a,2)^ROR(a,13)^ROR(a,22)) + ((a&b)^(a&c)^(b&c));
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    s->h[0]+=a; s->h[1]+=b; s->h[2]+=c; s->h[3]+=d; s->h[4]+=e; s->h[5]+=f; s->h[6]+=g; s->h[7]+=h;
}
static void sha_init(sha_t *s) {
    static const uint32_t iv[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
                                   0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    memcpy(s->h, iv, sizeof iv); s->len = 0; s->n = 0;
}
static void sha_upd(sha_t *s, const void *data, size_t n) {
    const uint8_t *p = data; s->len += n;
    while (n--) { s->b[s->n++] = *p++; if (s->n == 64) { sha_block(s, s->b); s->n = 0; } }
}
static void sha_fin(sha_t *s, uint8_t out[32]) {
    uint64_t bits = s->len * 8; uint8_t pad = 0x80, z = 0;
    sha_upd(s, &pad, 1);
    while (s->n != 56) sha_upd(s, &z, 1);
    for (int i = 7; i >= 0; i--) { uint8_t c = (uint8_t)(bits >> (8*i)); sha_upd(s, &c, 1); }
    for (int i = 0; i < 8; i++) {
        out[4*i] = s->h[i] >> 24; out[4*i+1] = s->h[i] >> 16; out[4*i+2] = s->h[i] >> 8; out[4*i+3] = s->h[i];
    }
}
/* H(part_1 || part_2 || ...) : variadic (ptr,len) pairs, n = number of pairs */
static void H(uint8_t out[32], int n, ...) {
    sha_t s; sha_init(&s);
    va_list ap; va_start(ap, n);
    for (int i = 0; i < n; i++) { const void *p = va_arg(ap, const void *); size_t l = va_arg(ap, size_t); sha_upd(&s, p, l); }
    va_end(ap);
    sha_fin(&s, out);
}

/* ---- little helpers for serialising values fed to H ---- */
static void ser16(uint8_t *o, const uint16_t *a) { for (int i = 0; i < N; i++) { o[2*i] = a[i] & 0xff; o[2*i+1] = a[i] >> 8; } }
static uint32_t ld32(const uint8_t *p) { uint32_t v = 0; for (int i = 0; i < 4; i++) v |= (uint32_t)p[i] << (8*i); return v; }
static uint64_t ld64(const uint8_t *p) { uint64_t v = 0; for (int i = 0; i < 8; i++) v |= (uint64_t)p[i] << (8*i); return v; }

/* ------------------------------------------------------- polynomial ring */
/* ternary poly (int8 in {-1,0,1}) times Z_q poly, in Z_q[x]/(x^N-1) */
static void mul_tern_zq(const int8_t *a, const uint16_t *b, uint16_t *c) {
    uint32_t acc[N]; memset(acc, 0, sizeof acc);
    for (int j = 0; j < N; j++) {
        if (!a[j]) continue;
        int pos = a[j] > 0;
        for (int k = 0; k < N - j; k++) acc[j + k] += pos ? b[k] : (uint32_t)(0 - b[k]);
        for (int k = N - j; k < N; k++) acc[j + k - N] += pos ? b[k] : (uint32_t)(0 - b[k]);
    }
    for (int i = 0; i < N; i++) c[i] = acc[i] & QMASK;
}
/* dense * dense mod (q, x^N-1) */
static void mul_dense(const uint16_t *a, const uint16_t *b, uint16_t *c) {
    uint32_t acc[N]; memset(acc, 0, sizeof acc);
    for (int i = 0; i < N; i++) {
        if (!a[i]) continue;
        for (int j = 0; j < N - i; j++) acc[i + j] += (uint32_t)a[i] * b[j];
        for (int j = N - i; j < N; j++) acc[i + j - N] += (uint32_t)a[i] * b[j];
    }
    for (int i = 0; i < N; i++) c[i] = acc[i] & QMASK;
}
static int center_q(uint16_t x) { return x > Q/2 ? (int)x - Q : (int)x; }   /* lift to (-q/2, q/2] */
static int mod_p(int v) { return ((v % P) + P) % P; }

/* L(a,b): a coefficients = +1, b coefficients = -1, rest 0 (partial Fisher-Yates) */
static void sample_L(int8_t *v, int a, int b) {
    int idx[N];
    memset(v, 0, N);
    for (int i = 0; i < N; i++) idx[i] = i;
    for (int i = 0; i < a + b; i++) {
        int j = i + (int)rnd_below(N - i), t = idx[i]; idx[i] = idx[j]; idx[j] = t;
        v[idx[i]] = i < a ? 1 : -1;
    }
}

/* ---- inversion in F_pr[x]/(x^N - 1), pr in {2,3}, via extended Euclid ---- */
static int pdeg(const int *a, int len) { for (int i = len - 1; i >= 0; i--) if (a[i]) return i; return -1; }
static int inv_modp(const int *f, int pr, int *out) {
    static int r0[N + 1], r1[N + 1], qq[N + 1], s0[2*N + 2], s1[2*N + 2], sn[2*N + 2];
    const int invp[3] = {0, 1, 2};
    memset(r0, 0, sizeof r0); memset(r1, 0, sizeof r1);
    memset(s0, 0, sizeof s0); memset(s1, 0, sizeof s1);
    r0[0] = pr - 1; r0[N] = 1;
    for (int i = 0; i < N; i++) r1[i] = f[i] % pr;
    s1[0] = 1;
    static int tmp[N + 1];
    for (;;) {
        int d1 = pdeg(r1, N + 1);
        if (d1 < 0) break;
        memset(qq, 0, sizeof qq);
        int d0 = pdeg(r0, N + 1);
        while (d0 >= d1) {
            int c = r0[d0] * invp[r1[d1]] % pr, sh = d0 - d1;
            qq[sh] = c;
            for (int i = 0; i <= d1; i++) r0[sh + i] = ((r0[sh + i] - c * r1[i]) % pr + pr) % pr;
            d0 = pdeg(r0, N + 1);
        }
        memset(sn, 0, sizeof sn);
        int ds1 = pdeg(s1, 2*N + 2);
        for (int i = 0; i <= N; i++) if (qq[i]) for (int j = 0; j <= ds1; j++) sn[i + j] = (sn[i + j] + qq[i] * s1[j]) % pr;
        for (int i = 0; i < 2*N + 2; i++) sn[i] = ((s0[i] - sn[i]) % pr + pr) % pr;
        /* (r0, r1) <- (r1, r0 mod r1) ; (s0, s1) <- (s1, sn) */
        memcpy(tmp, r0, sizeof tmp); memcpy(r0, r1, sizeof tmp); memcpy(r1, tmp, sizeof tmp);
        memcpy(s0, s1, sizeof s0); memcpy(s1, sn, sizeof s1);
    }
    if (pdeg(r0, N + 1) != 0) return 0;          /* gcd not a unit => not invertible */
    int ci = invp[r0[0]];
    memset(out, 0, N * sizeof(int));
    for (int i = 0; i < 2*N + 2; i++) out[i % N] = (out[i % N] + s0[i] * ci) % pr;
    return 1;
}

/* --------------------------------------------------------- NTRU key pair */
typedef struct {
    int8_t   f[N], g[N], fp[N];     /* private f, g ; f_p (balanced ternary) */
    uint16_t fq[N], h[N];           /* f_q ; public key h = g * f_q mod q   */
} ntru_key;

static void keygen(ntru_key *k) {
    for (;;) {
        sample_L(k->f, g_y, g_y - 1);
        sample_L(k->g, g_y, g_y);
        int f2[N], f3[N], i2[N], i3[N];
        for (int i = 0; i < N; i++) { f2[i] = k->f[i] & 1; f3[i] = mod_p(k->f[i]); }
        if (!inv_modp(f2, 2, i2)) continue;                 /* f must be invertible mod 2 (-> mod q) */
        if (!inv_modp(f3, P, i3)) continue;                 /* ... and mod p */
        uint16_t fm[N], b[N], t[N];
        for (int i = 0; i < N; i++) { fm[i] = (uint16_t)(k->f[i] & QMASK); b[i] = (uint16_t)i2[i]; }
        for (int it = 0; it < 4; it++) {                    /* Newton lift mod 2 -> 4 -> 16 -> 256 -> 65536 */
            mul_dense(fm, b, t);
            for (int i = 0; i < N; i++) t[i] = (uint16_t)(((i == 0 ? 2 : 0) - (int)t[i]) & QMASK);      /* t = 2 - f*b */
            uint16_t nb[N]; mul_dense(b, t, nb); memcpy(b, nb, sizeof b);
        }
        memcpy(k->fq, b, sizeof b);
        for (int i = 0; i < N; i++) k->fp[i] = (int8_t)(i3[i] == 2 ? -1 : i3[i]);
        mul_tern_zq(k->g, k->fq, k->h);                     /* h = g * f_q mod q */
        return;
    }
}

/* c = p*r*h + m  (mod q) */
static void ntru_encrypt(const uint16_t *h, const int8_t *r, const int8_t *m, uint16_t *c) {
    uint16_t t[N]; mul_tern_zq(r, h, t);
    for (int i = 0; i < N; i++) c[i] = (uint16_t)((P * (int)t[i] + m[i]) & QMASK);
}
/* K = (f*c mod q, centred) mod p */
static void derive_K(const int8_t *f, const uint16_t *c, uint8_t *K) {
    uint16_t b[N]; mul_tern_zq(f, c, b);
    for (int i = 0; i < N; i++) {
        int v = center_q(b[i]);
        if (abs(v) > g_maxabs) g_maxabs = abs(v);
        K[i] = (uint8_t)mod_p(v);
    }
}

/* ------------------------------------------------- Shamir over Z_M, M=2^61-1 */
static const uint64_t SM = (1ULL << 61) - 1;
static uint64_t mulm(uint64_t a, uint64_t b) { return (uint64_t)((unsigned __int128)a * b % SM); }
static uint64_t addm(uint64_t a, uint64_t b) { return (a + b) % SM; }
static uint64_t subm(uint64_t a, uint64_t b) { return (a + SM - b) % SM; }
static uint64_t powm(uint64_t a, uint64_t e) { uint64_t r = 1; while (e) { if (e & 1) r = mulm(r, a); a = mulm(a, a); e >>= 1; } return r; }
static uint64_t invm(uint64_t a) { return powm(a, SM - 2); }
static uint64_t shamir_eval(const uint64_t *coef, int k, uint64_t x) {
    uint64_t r = 0; for (int i = k - 1; i >= 0; i--) r = addm(mulm(r, x), coef[i]); return r;
}
static uint64_t shamir_recover(const uint32_t *xs, const uint64_t *ys, int k) {
    uint64_t s = 0;
    for (int i = 0; i < k; i++) {
        uint64_t num = 1, den = 1;
        for (int j = 0; j < k; j++) if (j != i) { num = mulm(num, xs[j]); den = mulm(den, subm(xs[j], xs[i])); }
        s = addm(s, mulm(ys[i], mulm(num, invm(den))));
    }
    return s;
}

/* ------------------------------------------------------------- PGAP actors */
typedef struct { uint16_t ei[N]; uint8_t ids[32]; }                 M2;
typedef struct { uint16_t e[N];  uint8_t v1[32]; }                  M3;
typedef struct { uint32_t m1; uint64_t m2; uint8_t v2[32]; }        M4;
typedef struct { uint8_t v3[32]; }                                  M5;

typedef struct { uint8_t ids_old[32], ids_cur[32]; uint16_t h[N]; } db_entry;
typedef struct { ntru_key key; uint8_t Ha0[32]; db_entry *D; int n, k; } server_t;
typedef struct { uint32_t x; uint64_t share; ntru_key key; uint16_t hs[N]; uint8_t ids[32]; } tag_t;
typedef struct { uint16_t ei[N], e[N]; uint8_t K[N]; } tag_sess;
typedef struct { int idx; uint8_t ids_rx[32]; uint16_t ei[N], e[N]; uint8_t K[N]; } srv_sess;

static const uint32_t P32 = P;

/* Step 2 (tag): e_i = p r_i * h + f_i */
static void tag_step2(tag_t *t, M2 *m, tag_sess *ts) {
    int8_t r[N]; sample_L(r, g_y, g_y);
    ntru_encrypt(t->hs, r, t->key.f, m->ei);
    memcpy(ts->ei, m->ei, sizeof m->ei);
    memcpy(m->ids, t->ids, 32);
}
/* Step 3 (server) */
static int srv_step3(server_t *S, const M2 *m2, M3 *m3, srv_sess *ss) {
    int idx = -1;
    for (int i = 0; i < S->n; i++)
        if (!memcmp(S->D[i].ids_cur, m2->ids, 32) || !memcmp(S->D[i].ids_old, m2->ids, 32)) { idx = i; break; }
    if (idx < 0) return 0;
    ss->idx = idx; memcpy(ss->ids_rx, m2->ids, 32); memcpy(ss->ei, m2->ei, sizeof ss->ei);
    int8_t r[N]; sample_L(r, g_y, g_y);
    ntru_encrypt(S->D[idx].h, r, S->key.f, m3->e);                /* e = p r h_i + f */
    memcpy(ss->e, m3->e, sizeof ss->e);
    derive_K(S->key.f, m2->ei, ss->K);                            /* K = (f*e_i mod q) mod p */
    uint8_t ei_b[2*N]; ser16(ei_b, m2->ei);
    H(m3->v1, 3, ss->K, (size_t)N, ei_b, sizeof ei_b, &P32, (size_t)4);
    return 1;
}
/* Step 4 (tag): verify V1, build M4 */
static int tag_step4(tag_t *t, tag_sess *ts, const M3 *m3, M4 *m4) {
    derive_K(t->key.f, m3->e, ts->K);
    memcpy(ts->e, m3->e, sizeof ts->e);
    uint8_t ei_b[2*N], e_b[2*N], v[32], hh[32];
    ser16(ei_b, ts->ei); ser16(e_b, ts->e);
    H(v, 3, ts->K, (size_t)N, ei_b, sizeof ei_b, &P32, (size_t)4);
    if (memcmp(v, m3->v1, 32)) return 0;                          /* server not authenticated */
    H(hh, 3, ts->K, (size_t)N, e_b, sizeof e_b, ei_b, sizeof ei_b);
    m4->m1 = t->x ^ ld32(hh);
    H(hh, 2, &t->x, (size_t)4, ts->K, (size_t)N);
    m4->m2 = t->share ^ ld64(hh);
    H(m4->v2, 2, &t->share, (size_t)8, ts->K, (size_t)N);
    return 1;
}
/* Step 5 (server): recover x_i, s(x_i); verify V2; update pseudonym; build M5 */
static int srv_step5(server_t *S, srv_sess *ss, const M4 *m4, M5 *m5, uint32_t *x_out, uint64_t *s_out) {
    uint8_t ei_b[2*N], e_b[2*N], hh[32], v2[32], ids_new[32];
    ser16(ei_b, ss->ei); ser16(e_b, ss->e);
    H(hh, 3, ss->K, (size_t)N, e_b, sizeof e_b, ei_b, sizeof ei_b);
    uint32_t x = m4->m1 ^ ld32(hh);
    H(hh, 2, &x, (size_t)4, ss->K, (size_t)N);
    uint64_t s = m4->m2 ^ ld64(hh);
    H(v2, 2, &s, (size_t)8, ss->K, (size_t)N);
    if (memcmp(v2, m4->v2, 32)) return 0;                         /* forged tag; D untouched */
    H(ids_new, 4, ss->ids_rx, (size_t)32, ss->K, (size_t)N, e_b, sizeof e_b, ei_b, sizeof ei_b);
    db_entry *d = &S->D[ss->idx];
    memcpy(d->ids_old, ss->ids_rx, 32);                           /* old <- received IDS */
    memcpy(d->ids_cur, ids_new, 32);
    H(m5->v3, 3, ss->K, (size_t)N, ids_new, (size_t)32, ei_b, sizeof ei_b);
    *x_out = x; *s_out = s;
    return 1;
}
/* Step 6 (tag): verify V3, update pseudonym */
static int tag_step6(tag_t *t, tag_sess *ts, const M5 *m5) {
    uint8_t ei_b[2*N], e_b[2*N], ids_new[32], v3[32];
    ser16(ei_b, ts->ei); ser16(e_b, ts->e);
    H(ids_new, 4, t->ids, (size_t)32, ts->K, (size_t)N, e_b, sizeof e_b, ei_b, sizeof ei_b);
    H(v3, 3, ts->K, (size_t)N, ids_new, (size_t)32, ei_b, sizeof ei_b);
    if (memcmp(v3, m5->v3, 32)) return 0;
    memcpy(t->ids, ids_new, 32);
    return 1;
}

/* ------------------------------------------------------------- system setup */
static void setup(server_t *S, tag_t *T, int n, int k, uint64_t *a0_out) {
    keygen(&S->key);
    S->n = n; S->k = k;
    S->D = calloc(n, sizeof(db_entry));
    uint64_t coef[64]; for (int i = 0; i < k; i++) coef[i] = rnd64() % SM;
    uint64_t a0 = coef[0]; *a0_out = a0;
    H(S->Ha0, 1, &a0, (size_t)8);
    for (int i = 0; i < n; i++) {
        T[i].x = (uint32_t)(i + 1);
        T[i].share = shamir_eval(coef, k, T[i].x);
        keygen(&T[i].key);
        memcpy(T[i].hs, S->key.h, sizeof T[i].hs);
        for (int j = 0; j < 32; j += 4) { uint32_t r = rnd32(); memcpy(T[i].ids + j, &r, 4); }
        memcpy(S->D[i].ids_cur, T[i].ids, 32); memcpy(S->D[i].ids_old, T[i].ids, 32);
        memcpy(S->D[i].h, T[i].key.h, sizeof T[i].key.h);
    }
}

/* one full honest session; drop5 / drop4 emulate message loss */
typedef struct { int ok3, ok4, ok5, ok6; uint32_t x; uint64_t s; uint8_t K_srv[N], K_tag[N]; M4 m4; } sess_res;
#define TR(...) do { if (g_trace) { printf("      > tag x_i=%-2u : ", t->x); printf(__VA_ARGS__); printf("\n"); } } while (0)
static sess_res run_session(server_t *S, tag_t *t, int drop4, int drop5) {
    sess_res r; memset(&r, 0, sizeof r);
    M2 m2; M3 m3; M4 m4; M5 m5; tag_sess ts; srv_sess ss;
    tag_step2(t, &m2, &ts);
    r.ok3 = srv_step3(S, &m2, &m3, &ss);
    if (!r.ok3) { TR("M2 rejected, pseudonym not found in database"); return r; }
    memcpy(r.K_srv, ss.K, N);
    r.ok4 = tag_step4(t, &ts, &m3, &m4);
    if (!r.ok4) { TR("V1 check FAILED at tag (server not authenticated)"); return r; }
    memcpy(r.K_tag, ts.K, N); r.m4 = m4;
    if (drop4) {
        TR("V1 ok | M4 LOST -> server did not update; IDS tag == server IDS_cur: %s",
           !memcmp(t->ids, S->D[ss.idx].ids_cur, 32) ? "YES" : "NO");
        return r;
    }
    r.ok5 = srv_step5(S, &ss, &m4, &m5, &r.x, &r.s);
    if (!r.ok5) { TR("V1 ok | V2 check FAILED at server (tag rejected, database unchanged)"); return r; }
    if (drop5) {
        TR("V1 ok, V2 ok | M5 LOST -> server updated IDS, tag kept old IDS; IDS tag == server IDS_old: %s",
           !memcmp(t->ids, S->D[ss.idx].ids_old, 32) ? "YES" : "NO");
        return r;
    }
    r.ok6 = tag_step6(t, &ts, &m5);
    TR("V1 ok, V2 ok, V3 %s | IDS updated, tag == server IDS_cur: %s, old IDS kept as IDS_old: %s",
       r.ok6 ? "ok" : "FAILED",
       !memcmp(t->ids, S->D[ss.idx].ids_cur, 32) ? "YES" : "NO",
       memcmp(S->D[ss.idx].ids_old, S->D[ss.idx].ids_cur, 32) ? "YES" : "NO");
    return r;
}

/* group verification: first k authorised, distinct shares -> Lagrange -> H(a0) */
static int group_verify(server_t *S, const uint32_t *xs, const uint64_t *ss, int cnt) {
    if (cnt < S->k) return 0;
    uint64_t a0 = shamir_recover(xs, ss, S->k);
    uint8_t h[32]; H(h, 1, &a0, (size_t)8);
    return !memcmp(h, S->Ha0, 32);
}


/* ====================================================================== */
int main(int argc, char **argv) {
    if (argc > 1) g_y = atoi(argv[1]);
    int pairs = argc > 2 ? atoi(argv[2]) : 100;
    int per   = argc > 3 ? atoi(argv[3]) : 20;

    printf("==================== PGAP verification (NTRU-509) ====================\n");
    printf("NTRU      : N = %d, p = %d, q = %d\n", N, P, Q);
    printf("Sets      : L_f = L(%d,%d) [%d non-zero], L_g = L_r = L(%d,%d) [%d non-zero]\n",
           g_y, g_y - 1, 2*g_y - 1, g_y, g_y, 2*g_y);
    printf("Group     : n = %d tags, threshold k = %d, Shamir field Z_p with prime 2^61-1\n", NTAGS, KTHR);
    printf("Hash      : SHA-256 (V1, V2, V3, masks, pseudonyms)   pseudonym IDS = 256 bits\n");
    printf("Run       : %d key pairs x %d sessions for the key-agreement test\n", pairs, per);
    printf("Wrap check: worst-case |3*r*g + f*f_i| = 3*%d + %d = %d  (< q/2 = %d : %s)\n",
           2*g_y, 2*g_y - 1, 3*2*g_y + 2*g_y - 1, Q/2, (3*2*g_y + 2*g_y - 1 < Q/2) ? "no wrap-around guaranteed" : "wrap-around possible");
    printf("=====================================================================\n\n");

    /* ---- R1: SHA-256 known-answer test ---- */
    printf("[R1] primitives\n");
    { uint8_t d[32]; H(d, 1, "abc", (size_t)3);
      static const uint8_t kat[4] = {0xba, 0x78, 0x16, 0xbf};
      OKMSG(!memcmp(d, kat, 4) && d[31] == 0xad, "SHA-256(\"abc\") = ba7816bf...15ad"); }

    /* ---- R2: NTRU key generation ---- */
    printf("[R2] NTRU key generation (50 keys)\n");
    { int bad_fq = 0, bad_fp = 0, bad_h = 0;
      for (int t = 0; t < 50; t++) {
          ntru_key k; keygen(&k);
          uint16_t chk[N]; mul_tern_zq(k.f, k.fq, chk);
          for (int i = 0; i < N; i++) if (chk[i] != (i == 0)) { bad_fq++; break; }
          /* f * f_p = 1 mod 3 : compute with int arithmetic */
          int acc[N]; memset(acc, 0, sizeof acc);
          for (int i = 0; i < N; i++) if (k.f[i]) for (int j = 0; j < N; j++) acc[(i + j) % N] += k.f[i] * k.fp[j];
          for (int i = 0; i < N; i++) if (mod_p(acc[i]) != (i == 0)) { bad_fp++; break; }
          mul_tern_zq(k.f, k.h, chk);                         /* f*h should equal g mod q */
          for (int i = 0; i < N; i++) if (center_q(chk[i]) != k.g[i]) { bad_h++; break; }
      }
      OKMSG(!bad_fq, "f * f_q = 1 (mod q)   [%d failures / 50]", bad_fq);
      OKMSG(!bad_fp, "f * f_p = 1 (mod p)   [%d failures / 50]", bad_fp);
      OKMSG(!bad_h,  "f * h   = g (mod q)   [%d failures / 50]", bad_h); }

    /* ---- R3: Shamir ---- */
    printf("[R3] Shamir (k=5, n=10, prime field Z_(2^61-1))\n");
    { uint64_t coef[5]; for (int i = 0; i < 5; i++) coef[i] = rnd64() % SM;
      uint32_t xs[10]; uint64_t ys[10];
      for (int i = 0; i < 10; i++) { xs[i] = i + 1; ys[i] = shamir_eval(coef, 5, xs[i]); }
      int ok = 1; for (int t = 0; t < 200; t++) {
          uint32_t sx[5]; uint64_t sy[5]; int used[10] = {0};
          for (int j = 0; j < 5; j++) { int c; do c = rnd_below(10); while (used[c]); used[c] = 1; sx[j] = xs[c]; sy[j] = ys[c]; }
          if (shamir_recover(sx, sy, 5) != coef[0]) ok = 0; }
      OKMSG(ok, "any 5 of 10 shares recover a0 (200 random subsets)");
      OKMSG(shamir_recover(xs, ys, 4) != coef[0], "only 4 shares do NOT recover a0");
      /* the paper suggests r = q (=2048): Z_2048 is a ring, not a field */
      int has_inv = 0; for (int u = 1; u < Q; u++) if ((2 * u) % Q == 1) has_inv = 1;
      OKMSG(!has_inv, "r=q=2048 is not a field: x_j-x_i=2 has no inverse mod 2048 (so r must be prime)"); }

    /* ---- R4: single session, correctness ---- */
    printf("[R4] one full session (Steps 1-6)\n");
    server_t S; tag_t T[NTAGS]; uint64_t a0;
    setup(&S, T, NTAGS, KTHR, &a0);
    { uint8_t ids0[32]; memcpy(ids0, T[0].ids, 32);
      g_trace = 1;
      sess_res r = run_session(&S, &T[0], 0, 0);
      g_trace = 0;
      OKMSG(r.ok3 && r.ok4 && r.ok5 && r.ok6, "V1, V2, V3 all verify");
      OKMSG(!memcmp(r.K_srv, r.K_tag, N), "K (server) == K_i (tag), %d coefficients", N);
      OKMSG(r.x == T[0].x && r.s == T[0].share, "server recovered x_i and s(x_i) correctly");
      OKMSG(!memcmp(T[0].ids, S.D[0].ids_cur, 32) && memcmp(T[0].ids, ids0, 32), "pseudonym updated and synchronised");
      OKMSG(!memcmp(S.D[0].ids_old, ids0, 32), "server kept the previous IDS as IDS_old"); }

    /* ---- R5: group authentication ---- */
    printf("[R5] group authentication, n=10, k=5\n");
    { uint32_t xs[10]; uint64_t ys[10]; int cnt = 0;
      g_trace = 1;
      for (int i = 0; i < 10; i++) { sess_res r = run_session(&S, &T[i], 0, 0); if (r.ok5) { xs[cnt] = r.x; ys[cnt++] = r.s; } }
      g_trace = 0;
      int gok = group_verify(&S, xs, ys, cnt);
      printf("  >>> GROUP AUTHENTICATION (all tags): %s   [authorised %d/%d tags, threshold k=%d]\n",
             gok ? "SUCCESS" : "FAILED", cnt, NTAGS, KTHR);
      OKMSG(cnt == NTAGS, "all %d honest tags authorised (V1, V2, V3 verified, IDS updated and matching)", NTAGS);
      OKMSG(gok, "H(a0) recovered from k shares matches stored H(a0)");
      int g4 = group_verify(&S, xs, ys, KTHR - 1);
      printf("  >>> GROUP AUTHENTICATION (only %d valid tags): %s\n", KTHR - 1, g4 ? "SUCCESS" : "FAILED (fewer than k)");
      OKMSG(!g4, "only %d valid tags (< k) -> group authentication fails", KTHR - 1); }

    /* ---- R6: forged tag ---- */
    printf("[R6] forged tag (knows IDS and h, but not f_i)\n");
    { tag_t forger = T[2]; keygen(&forger.key);               /* same IDS/x/share, wrong private key */
      db_entry before = S.D[2];
      M2 m2; M3 m3; M4 m4; M5 m5; tag_sess ts; srv_sess ss; uint32_t x; uint64_t s;
      tag_step2(&forger, &m2, &ts);
      int a = srv_step3(&S, &m2, &m3, &ss);
      int b = tag_step4(&forger, &ts, &m3, &m4);
      OKMSG(a && !b, "forger cannot validate V1 (cannot derive K) -> server is also authenticated to the real tag only");
      m4.m1 = rnd32(); m4.m2 = rnd64(); for (int i = 0; i < 32; i++) m4.v2[i] = rnd32();
      int c = srv_step5(&S, &ss, &m4, &m5, &x, &s);
      OKMSG(!c, "server rejects forged M4 (V2 mismatch)");
      OKMSG(!memcmp(&before, &S.D[2], sizeof before), "database entry unchanged"); }

    /* ---- R7: message loss / desynchronisation ---- */
    printf("[R7] desynchronisation resilience (message loss)\n");
    { tag_t *t = &T[3]; sess_res r;
      g_trace = 1;
      r = run_session(&S, t, 1, 0);                           /* M4 lost */
      OKMSG(r.ok4 && !r.ok5 && !memcmp(t->ids, S.D[3].ids_cur, 32), "M4 lost: neither side updated, still in sync");
      r = run_session(&S, t, 0, 1);                           /* M5 lost */
      OKMSG(r.ok5 && !r.ok6 && !memcmp(t->ids, S.D[3].ids_old, 32), "M5 lost: tag holds IDS_old of the server");
      r = run_session(&S, t, 0, 1);                           /* M5 lost again */
      OKMSG(r.ok3 && r.ok5 && !r.ok6, "M5 lost twice in a row: server still finds the tag");
      r = run_session(&S, t, 0, 0);                           /* delivered */
      OKMSG(r.ok6 && !memcmp(t->ids, S.D[3].ids_cur, 32), "next delivered session resynchronises");
      g_trace = 0; }

    /* ---- R8: decryption failure / key mismatch, fresh random keys ---- */
    printf("[R8] key agreement over %d key pairs x %d sessions\n", pairs, per);
    { long mism = 0, tot = 0, naive_mism = 0; g_maxabs = 0;
      for (int kp = 0; kp < pairs; kp++) {
          ntru_key sk, tk; keygen(&sk); keygen(&tk);
          for (int s = 0; s < per; s++) {
              int8_t r1[N], r2[N]; sample_L(r1, g_y, g_y); sample_L(r2, g_y, g_y);
              uint16_t ei[N], e[N]; uint8_t Ks[N], Kt[N];
              ntru_encrypt(sk.h, r1, tk.f, ei);                /* tag -> server */
              ntru_encrypt(tk.h, r2, sk.f, e);                 /* server -> tag */
              derive_K(sk.f, ei, Ks); derive_K(tk.f, e, Kt);
              if (memcmp(Ks, Kt, N)) mism++;
              /* naive "b mod p" on the residue in [0,q) instead of the centred lift */
              uint16_t b1[N], b2[N]; mul_tern_zq(sk.f, ei, b1); mul_tern_zq(tk.f, e, b2);
              for (int i = 0; i < N; i++) if (b1[i] % P != b2[i] % P) { naive_mism++; break; }
              tot++;
          } }
      printf("  max |coeff of f*e mod q| observed = %d  (limit %d)\n", g_maxabs, Q/2 - 1);
      OKMSG(mism == 0, "K != K_i in %ld / %ld sessions (centred lift)", mism, tot);
      printf("  [info] naive 'residue in [0,q) mod p' (no centring) would break key agreement in %ld / %ld sessions\n",
             naive_mism, tot); }

    /* ---- R9: security observations that follow from the protocol as specified ---- */
    printf("[R9] protocol-level findings (observations, not pass/fail tests)\n");
    { tag_t *t = &T[5];
      sess_res a = run_session(&S, t, 0, 0), b = run_session(&S, t, 0, 0);
      int sameK = !memcmp(a.K_srv, b.K_srv, N), same_m2 = a.m4.m2 == b.m4.m2, same_v2 = !memcmp(a.m4.v2, b.m4.v2, 32);
      printf("  [obs] K identical in two sessions of the same tag: %s  (K = f*f_i mod p depends only on long-term keys)\n", sameK ? "YES" : "no");
      printf("  [obs] m2 identical across sessions: %s ; V2 identical across sessions: %s  -> linkable despite pseudonyms\n",
             same_m2 ? "YES" : "no", same_v2 ? "YES" : "no");
      /* the tag can decrypt e = p r h_i + f exactly like an NTRU ciphertext and recover f */
      int8_t rr[N]; sample_L(rr, g_y, g_y); uint16_t e[N], bq[N];
      ntru_encrypt(t->key.h, rr, S.key.f, e);
      mul_tern_zq(t->key.f, e, bq);
      int acc[N]; memset(acc, 0, sizeof acc);
      for (int i = 0; i < N; i++) { int ci = center_q(bq[i]); if (ci) for (int j = 0; j < N; j++) acc[(i + j) % N] += ci * t->key.fp[j]; }
      int rec = 1; for (int i = 0; i < N; i++) { int v = mod_p(acc[i]); if (v == 2) v = -1; if (v != S.key.f[i]) rec = 0; }
      printf("  [obs] a tag recovers the server's PRIVATE key f from M3 using its own f_i, f_ip: %s\n", rec ? "YES" : "no");
      /* an attacker holding f then derives K for any other tag from a sniffed e_i */
      M2 m2; tag_sess ts; tag_step2(&T[7], &m2, &ts);
      uint8_t Katk[N], Ktrue[N]; derive_K(S.key.f, m2.ei, Katk);     /* attacker uses recovered f */
      srv_sess ss; M3 m3; srv_step3(&S, &m2, &m3, &ss); memcpy(Ktrue, ss.K, N);
      printf("  [obs] holder of f derives the session key K of ANOTHER tag from a sniffed M2: %s\n", !memcmp(Katk, Ktrue, N) ? "YES" : "no");
      /* corrupted share passes V2 */
      tag_t bad = T[8]; bad.share = addm(bad.share, 1);
      sess_res c = run_session(&S, &bad, 0, 0);
      printf("  [obs] tag with valid key but corrupted share passes V2: %s (V2 only proves knowledge of K)\n", c.ok5 ? "YES" : "no");
      memcpy(T[8].ids, bad.ids, 32); }

    printf("\n=== %ld checks, %ld failed ===\n", g_checks, g_fail);
    free(S.D);
    return g_fail ? 1 : 0;
}
