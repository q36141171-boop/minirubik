#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PERMUTATIONS 5040
#define ORIENTATIONS 729
#define CUBIES 7

static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};
static const char *move_names[9] = {
    "R", "R2", "R'", "B", "B2", "B'", "D", "D2", "D'"
};

// Factored quarter-turn transition tables (~34.6 KiB)
static uint16_t next_p[PERMUTATIONS][3];
static uint16_t next_o[ORIENTATIONS][3];

// 4-bit Nibble Packed PDB tables (< 3 KiB)
static uint8_t pdb_p_packed[PERMUTATIONS / 2];
static uint8_t pdb_o_packed[(ORIENTATIONS + 1) / 2];

// Unranking & Ranking
static void unrank_p(uint16_t rank, uint8_t p[CUBIES]) {
    uint8_t avail[CUBIES];
    for (int i = 0; i < CUBIES; i++) avail[i] = i;
    int fact = 720;
    for (int i = 0; i < CUBIES - 1; i++) {
        int idx = rank / fact;
        rank %= fact;
        p[i] = avail[idx];
        for (int j = idx; j < CUBIES - 1 - i; j++) avail[j] = avail[j + 1];
        fact /= (CUBIES - 1 - i);
    }
    p[CUBIES - 1] = avail[0];
}

static uint16_t rank_p(const uint8_t p[CUBIES]) {
    uint16_t rank = 0;
    for (int i = 0; i < CUBIES; ++i) {
        uint16_t smaller = 0;
        for (int j = i + 1; j < CUBIES; ++j) {
            if (p[j] < p[i]) ++smaller;
        }
        rank = rank * (CUBIES - i) + smaller;
    }
    return rank;
}

static void unrank_o(uint16_t rank, uint8_t o[CUBIES]) {
    uint8_t sum = 0;
    for (int i = 5; i >= 0; i--) {
        o[i] = rank % 3;
        sum += o[i];
        rank /= 3;
    }
    o[6] = (3 - (sum % 3)) % 3;
}

static uint16_t rank_o(const uint8_t o[CUBIES]) {
    uint16_t rank = 0;
    for (int i = 0; i < 6; i++) {
        rank = rank * 3 + o[i];
    }
    return rank;
}

// Build transition tables
static void build_transition_tables(void) {
    uint8_t p[CUBIES], p2[CUBIES];
    uint8_t o[CUBIES], o2[CUBIES];
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
            for (int i = 0; i < CUBIES; i++) {
                o2[i] = (o[source[f][i]] + twist[f][i]) % 3;
            }
            next_o[r][f] = rank_o(o2);
        }
    }
}

// Nibble packing helpers
static inline void set_pdb_val(uint8_t *table, int idx, uint8_t val) {
    if (idx & 1) table[idx >> 1] = (table[idx >> 1] & 0x0F) | (val << 4);
    else         table[idx >> 1] = (table[idx >> 1] & 0xF0) | (val & 0x0F);
}

static inline uint8_t get_pdb_val(const uint8_t *table, int idx) {
    uint8_t b = table[idx >> 1];
    return (idx & 1) ? (b >> 4) : (b & 0x0F);
}

// Retrograde BFS to generate PDBs
static void build_pdbs(void) {
    memset(pdb_p_packed, 0xFF, sizeof(pdb_p_packed));
    memset(pdb_o_packed, 0xFF, sizeof(pdb_o_packed));
    
    // BFS for Permutation PDB
    static uint16_t q_p[PERMUTATIONS];
    int head = 0, tail = 0;
    q_p[tail++] = 0;
    set_pdb_val(pdb_p_packed, 0, 0);
    while (head < tail) {
        uint16_t u = q_p[head++];
        uint8_t dist = get_pdb_val(pdb_p_packed, u);
        for (int f = 0; f < 3; f++) {
            uint16_t v = u;
            for (int turns = 1; turns <= 3; turns++) {
                v = next_p[v][f];
                if (get_pdb_val(pdb_p_packed, v) == 0x0F) { // unvisited
                    set_pdb_val(pdb_p_packed, v, dist + 1);
                    q_p[tail++] = v;
                }
            }
        }
    }

    // BFS for Orientation PDB
    static uint16_t q_o[ORIENTATIONS];
    head = 0; tail = 0;
    q_o[tail++] = 0;
    set_pdb_val(pdb_o_packed, 0, 0);
    while (head < tail) {
        uint16_t u = q_o[head++];
        uint8_t dist = get_pdb_val(pdb_o_packed, u);
        for (int f = 0; f < 3; f++) {
            uint16_t v = u;
            for (int turns = 1; turns <= 3; turns++) {
                v = next_o[v][f];
                if (get_pdb_val(pdb_o_packed, v) == 0x0F) {
                    set_pdb_val(pdb_o_packed, v, dist + 1);
                    q_o[tail++] = v;
                }
            }
        }
    }
}

// Non-recursive IDA* Search Frame
typedef struct {
    uint16_t p, o;
    int prev_face;
    int move_idx;
} StackFrame;

static int solve_ida(uint16_t start_p, uint16_t start_o) {
    uint8_t h0_p = get_pdb_val(pdb_p_packed, start_p);
    uint8_t h0_o = get_pdb_val(pdb_o_packed, start_o);
    int bound = (h0_p > h0_o) ? h0_p : h0_o;

    StackFrame stack[16];
    int solution[16];

    while (bound <= 11) {
        int depth = 0;
        stack[0].p = start_p;
        stack[0].o = start_o;
        stack[0].prev_face = -1;
        stack[0].move_idx = 0;

        int next_bound = 99;

        while (depth >= 0) {
            uint16_t cur_p = stack[depth].p;
            uint16_t cur_o = stack[depth].o;

            if (cur_p == 0 && cur_o == 0) {
                // Solution found!
                for (int i = 0; i < depth; i++) {
                    printf("%s ", move_names[solution[i]]);
                }
                printf("\nFound optimal solution in %d moves.\n", depth);
                return depth;
            }

            if (stack[depth].move_idx >= 9) {
                depth--;
                if (depth >= 0) stack[depth].move_idx++;
                continue;
            }

            int m = stack[depth].move_idx;
            int f = m / 3;
            int turns = (m % 3) + 1;

            // Pruning: skip same face
            if (f == stack[depth].prev_face) {
                stack[depth].move_idx++;
                continue;
            }

            // Apply move via precomputed transitions
            uint16_t np = cur_p;
            uint16_t no = cur_o;
            for (int t = 0; t < turns; t++) {
                np = next_p[np][f];
                no = next_o[no][f];
            }

            uint8_t hp = get_pdb_val(pdb_p_packed, np);
            uint8_t ho = get_pdb_val(pdb_o_packed, no);
            uint8_t h = (hp > ho) ? hp : ho;
            int f_score = (depth + 1) + h;

            if (f_score > bound) {
                if (f_score < next_bound) next_bound = f_score;
                stack[depth].move_idx++;
                continue;
            }

            // Push forward
            solution[depth] = m;
            depth++;
            stack[depth].p = np;
            stack[depth].o = no;
            stack[depth].prev_face = f;
            stack[depth].move_idx = 0;
        }
        bound = next_bound;
    }
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 2 || strlen(argv[1]) != 14) {
        printf("Usage: %s <14-char state string>\n", argv[0]);
        return 1;
    }

    printf("Building transition tables and PDBs on host...\n");
    build_transition_tables();
    build_pdbs();
    printf("Perm PDB: %lu bytes, Orient PDB: %lu bytes\n", 
           sizeof(pdb_p_packed), sizeof(pdb_o_packed));

    uint8_t p[CUBIES], o[CUBIES];
    for (int i = 0; i < CUBIES; i++) {
        p[i] = argv[1][i] - '1';
        o[i] = argv[1][i + 7] - '1';
    }

    uint16_t sp = rank_p(p);
    uint16_t so = rank_o(o);

    printf("Searching solution for [%s] (p=%d, o=%d)...\n", argv[1], sp, so);
    solve_ida(sp, so);

    return 0;
}
