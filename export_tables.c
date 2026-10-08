#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PERMUTATIONS 5040
#define ORIENTATIONS 729
#define CUBIES 7

static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6}, {0, 1, 2, 4, 5, 6, 3}, {0, 2, 5, 3, 1, 4, 6}
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0}, {0, 0, 0, 1, 2, 1, 2}, {0, 0, 0, 0, 0, 0, 0}
};

static uint16_t next_p[PERMUTATIONS][3];
static uint16_t next_o[ORIENTATIONS][3];
static uint8_t pdb_p_packed[PERMUTATIONS / 2];
static uint8_t pdb_o_packed[(ORIENTATIONS + 1) / 2];

static void unrank_p(uint16_t rank, uint8_t p[CUBIES]) {
    uint8_t avail[CUBIES];
    for (int i = 0; i < CUBIES; i++) avail[i] = i;
    int fact = 720;
    for (int i = 0; i < CUBIES - 1; i++) {
        int idx = rank / fact; rank %= fact; p[i] = avail[idx];
        for (int j = idx; j < CUBIES - 1 - i; j++) avail[j] = avail[j + 1];
        fact /= (CUBIES - 1 - i);
    }
    p[CUBIES - 1] = avail[0];
}

static uint16_t rank_p(const uint8_t p[CUBIES]) {
    uint16_t rank = 0;
    for (int i = 0; i < CUBIES; ++i) {
        uint16_t smaller = 0;
        for (int j = i + 1; j < CUBIES; ++j) if (p[j] < p[i]) ++smaller;
        rank = rank * (CUBIES - i) + smaller;
    }
    return rank;
}

static void unrank_o(uint16_t rank, uint8_t o[CUBIES]) {
    uint8_t sum = 0;
    for (int i = 5; i >= 0; i--) { o[i] = rank % 3; sum += o[i]; rank /= 3; }
    o[6] = (3 - (sum % 3)) % 3;
}

static uint16_t rank_o(const uint8_t o[CUBIES]) {
    uint16_t rank = 0;
    for (int i = 0; i < 6; i++) rank = rank * 3 + o[i];
    return rank;
}

static inline void set_pdb_val(uint8_t *t, int idx, uint8_t v) {
    if (idx & 1) t[idx >> 1] = (t[idx >> 1] & 0x0F) | (v << 4);
    else         t[idx >> 1] = (t[idx >> 1] & 0xF0) | (v & 0x0F);
}

static inline uint8_t get_pdb_val(const uint8_t *t, int idx) {
    uint8_t b = t[idx >> 1];
    return (idx & 1) ? (b >> 4) : (b & 0x0F);
}

int main(void) {
    // 1. Build transition tables
    uint8_t p[CUBIES], p2[CUBIES], o[CUBIES], o2[CUBIES];
    for (int r = 0; r < PERMUTATIONS; r++) {
        unrank_p(r, p);
        for (int f = 0; f < 3; f++) {
            for (int i = 0; i < CUBIES; i++) p2[i] = p[source[f][i]];
            next_p[r][f] = rank_p(p2);
        }
    }
    for (int r = 0; r < ORIENTATIONS; r++) {
        unrank_o(r, o);
        for (int f = 0; f < 3; f++) {
            for (int i = 0; i < CUBIES; i++) o2[i] = (o[source[f][i]] + twist[f][i]) % 3;
            next_o[r][f] = rank_o(o2);
        }
    }

    // 2. Build PDBs
    memset(pdb_p_packed, 0xFF, sizeof(pdb_p_packed));
    memset(pdb_o_packed, 0xFF, sizeof(pdb_o_packed));
    static uint16_t q_p[PERMUTATIONS], q_o[ORIENTATIONS];
    int h = 0, t = 0;
    q_p[t++] = 0; set_pdb_val(pdb_p_packed, 0, 0);
    while (h < t) {
        uint16_t u = q_p[h++]; uint8_t dist = get_pdb_val(pdb_p_packed, u);
        for (int f = 0; f < 3; f++) {
            uint16_t v = u;
            for (int turn = 1; turn <= 3; turn++) {
                v = next_p[v][f];
                if (get_pdb_val(pdb_p_packed, v) == 0x0F) {
                    set_pdb_val(pdb_p_packed, v, dist + 1); q_p[t++] = v;
                }
            }
        }
    }

    h = 0; t = 0;
    q_o[t++] = 0; set_pdb_val(pdb_o_packed, 0, 0);
    while (h < t) {
        uint16_t u = q_o[h++]; uint8_t dist = get_pdb_val(pdb_o_packed, u);
        for (int f = 0; f < 3; f++) {
            uint16_t v = u;
            for (int turn = 1; turn <= 3; turn++) {
                v = next_o[v][f];
                if (get_pdb_val(pdb_o_packed, v) == 0x0F) {
                    set_pdb_val(pdb_o_packed, v, dist + 1); q_o[t++] = v;
                }
            }
        }
    }

    // 3. Export to tables.s
    FILE *fp = fopen("tables.s", "w");
    if (!fp) return 1;

    fprintf(fp, ".section .rodata\n.align 2\n\n");
    fprintf(fp, ".globl next_p\nnext_p:\n");
    for (int r = 0; r < PERMUTATIONS; r++) {
        fprintf(fp, "  .half %d, %d, %d\n", next_p[r][0], next_p[r][1], next_p[r][2]);
    }

    fprintf(fp, "\n.align 2\n.globl next_o\nnext_o:\n");
    for (int r = 0; r < ORIENTATIONS; r++) {
        fprintf(fp, "  .half %d, %d, %d\n", next_o[r][0], next_o[r][1], next_o[r][2]);
    }

    fprintf(fp, "\n.globl pdb_p_packed\npdb_p_packed:\n");
    for (int i = 0; i < sizeof(pdb_p_packed); i++) {
        if (i % 16 == 0) fprintf(fp, "  .byte ");
        fprintf(fp, "0x%02x%s", pdb_p_packed[i], (i % 16 == 15 || i == sizeof(pdb_p_packed) - 1) ? "\n" : ", ");
    }

    fprintf(fp, "\n.globl pdb_o_packed\npdb_o_packed:\n");
    for (int i = 0; i < sizeof(pdb_o_packed); i++) {
        if (i % 16 == 0) fprintf(fp, "  .byte ");
        fprintf(fp, "0x%02x%s", pdb_o_packed[i], (i % 16 == 15 || i == sizeof(pdb_o_packed) - 1) ? "\n" : ", ");
    }

    fclose(fp);
    printf("Successfully generated tables.s (~37.5 KiB)\n");
    return 0;
}
