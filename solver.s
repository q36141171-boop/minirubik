.section .text
.globl main

# ==============================================================================
# Helper 1: get_pdb_val
# 輸入: a0 = rank (0-5039 或 0-728), a1 = table_base_address
# 輸出: a0 = distance (0-11)
# ==============================================================================
get_pdb_val:
    srli  t0, a0, 1           # t0 = rank / 2 (byte 偏移量)
    add   t0, a1, t0           # t0 = table_base + offset
    lbu   t1, 0(t0)           # 讀出該 byte (內含兩個 4-bit 狀態)
    andi  t2, a0, 1           # 檢查 index 是奇數還是偶數
    beqz  t2, .L_even_nibble
    srli  a0, t1, 4           # 奇數: 取高 4 bits
    ret
.L_even_nibble:
    andi  a0, t1, 0x0F        # 偶數: 取低 4 bits
    ret

# ==============================================================================
# Helper 2: lookup_next
# 輸入: a0 = rank, a1 = face (0:R, 1:B, 2:D), a2 = table_base
# 輸出: a0 = new_rank
# 公式: base + 2 * (rank * 3 + face)，全程不用乘法
# ==============================================================================
lookup_next:
    slli  t0, a0, 1           # t0 = rank * 2
    add   t0, t0, a0           # t0 = rank * 3
    add   t0, t0, a1           # t0 = rank * 3 + face
    slli  t0, t0, 1           # t0 = (rank * 3 + face) * 2 (half-word)
    add   t0, a2, t0           # 加上表格基底位址
    lhu   a0, 0(t0)           # 讀取 16-bit 下一狀態 rank
    ret

# ==============================================================================
# IDA* Search Core (Non-recursive)
# 參數: a0 = start_p, a1 = start_o
# 回傳: a0 = 最少還原步數 (optimal depth)
# ==============================================================================
solve_ida:
    # 堆疊配置:
    # - 保存 callee-saved 暫存器 s0-s11, ra (共 52 bytes)
    # - 搜尋堆疊: 最大深度 12，每層 16 bytes:
    #     0(sp): cur_p (2 bytes)
    #     2(sp): cur_o (2 bytes)
    #     4(sp): prev_face (4 bytes)
    #     8(sp): move_idx (4 bytes)
    # 總堆疊空間: 256 bytes (維持 16-byte 對齊)
    addi  sp, sp, -256
    sw    ra, 252(sp)
    sw    s0, 248(sp)
    sw    s1, 244(sp)
    sw    s2, 240(sp)
    sw    s3, 236(sp)
    sw    s4, 232(sp)
    sw    s5, 228(sp)
    sw    s6, 224(sp)
    sw    s7, 220(sp)
    sw    s8, 216(sp)

    mv    s0, a0              # s0 = start_p
    mv    s1, a1              # s1 = start_o

    # 1. 計算根節點啟發值 h0 = max(PDB_p[start_p], PDB_o[start_o])
    la    a1, pdb_p_packed
    mv    a0, s0
    jal   ra, get_pdb_val
    mv    s2, a0              # s2 = hp

    la    a1, pdb_o_packed
    mv    a0, s1
    jal   ra, get_pdb_val
    mv    s3, a0              # s3 = ho

    bge   s2, s3, .L_init_bound
    mv    s2, s3              # s2 = initial bound = max(hp, ho)

.L_init_bound:
    mv    s4, s2              # s4 = bound

.L_outer_bound_loop:
    li    t0, 11
    bgt   s4, t0, .L_search_failed  # 超過直徑 11 步則中止

    li    s5, 0               # s5 = depth = 0
    li    s6, 99              # s6 = next_bound = 99

    # 初始化 root frame (depth 0): frame_addr = sp + depth * 16
    sh    s0, 0(sp)           # stack[0].p = start_p
    sh    s1, 2(sp)           # stack[0].o = start_o
    li    t0, -1
    sw    t0, 4(sp)           # stack[0].prev_face = -1
    sw    x0, 8(sp)           # stack[0].move_idx = 0

.L_dfs_loop:
    blt   s5, x0, .L_dfs_end  # if depth < 0, 當前 bound 搜尋完畢

    # 取得當前 depth 的 frame 位址: t0 = sp + (depth << 4)
    slli  t0, s5, 4
    add   s7, sp, t0          # s7 = &stack[depth]

    lhu   s8, 0(s7)           # s8 = cur_p
    lhu   s9, 2(s7)           # s9 = cur_o

    # 檢查是否到達還原狀態 (p == 0 && o == 0)
    or    t1, s8, s9
    beqz  t1, .L_search_success

    # 讀取當前 move_idx
    lw    t2, 8(s7)
    li    t3, 9
    blt   t2, t3, .L_try_move

    # 當前節點所有 9 個分支皆試完，回溯 (Backtrack)
    addi  s5, s5, -1          # depth--
    blt   s5, x0, .L_dfs_loop
    slli  t0, s5, 4
    add   t0, sp, t0
    lw    t1, 8(t0)
    addi  t1, t1, 1
    sw    t1, 8(t0)           # stack[depth].move_idx++
    j     .L_dfs_loop

.L_try_move:
    # m = move_idx (0..8)
    # 分解面 f = m / 3 與轉動角度 turns = (m % 3) + 1 (消除除法)
    # m < 3: f=0, turns=m+1
    # m < 6: f=1, turns=(m-3)+1
    # m >= 6: f=2, turns=(m-6)+1
    li    t4, 3
    blt   t2, t4, .L_m_face0
    li    t4, 6
    blt   t2, t4, .L_m_face1
    # Face 2 (D)
    li    s10, 2              # s10 = face
    addi  s11, t2, -5         # turns = (m - 6) + 1 = m - 5
    j     .L_check_prune
.L_m_face0:
    li    s10, 0              # face = 0 (R)
    addi  s11, t2, 1          # turns = m + 1
    j     .L_check_prune
.L_m_face1:
    li    s10, 1              # face = 1 (B)
    addi  s11, t2, -2         # turns = (m - 3) + 1 = m - 2

.L_check_prune:
    # Cayley Graph Pruning: 避免連續轉動同一個面
    lw    t3, 4(s7)           # prev_face
    beq   s10, t3, .L_skip_this_move

    # 計算轉動 turns 次後的 np, no
    mv    a0, s8
    mv    a1, s10
    la    a2, next_p
    jal   ra, lookup_next
    mv    t5, a0              # t5 = np (1 turn)

    mv    a0, s9
    mv    a1, s10
    la    a2, next_o
    jal   ra, lookup_next
    mv    t6, a0              # t6 = no (1 turn)

    li    t0, 1
    beq   s11, t0, .L_eval_heuristic

    # 轉第 2 次
    mv    a0, t5
    mv    a1, s10
    la    a2, next_p
    jal   ra, lookup_next
    mv    t5, a0

    mv    a0, t6
    mv    a1, s10
    la    a2, next_o
    jal   ra, lookup_next
    mv    t6, a0

    li    t0, 2
    beq   s11, t0, .L_eval_heuristic

    # 轉第 3 次
    mv    a0, t5
    mv    a1, s10
    la    a2, next_p
    jal   ra, lookup_next
    mv    t5, a0

    mv    a0, t6
    mv    a1, s10
    la    a2, next_o
    jal   ra, lookup_next
    mv    t6, a0

.L_eval_heuristic:
    # 評估啟發值 h = max(PDB_p[np], PDB_o[no])
    addi  sp, sp, -8
    sw    t5, 0(sp)
    sw    t6, 4(sp)

    mv    a0, t5
    la    a1, pdb_p_packed
    jal   ra, get_pdb_val
    mv    t4, a0              # t4 = hp

    lw    t6, 4(sp)
    mv    a0, t6
    la    a1, pdb_o_packed
    jal   ra, get_pdb_val
    mv    t3, a0              # t3 = ho
    lw    t5, 0(sp)
    addi  sp, sp, 8

    # 取 max
    bge   t4, t3, .L_got_h
    mv    t4, t3
.L_got_h:
    # f_score = (depth + 1) + h
    addi  t0, s5, 1
    add   t0, t0, t4

    # 檢查是否超出 bound
    ble   t0, s4, .L_push_next_depth

    # 超出 bound，更新 next_bound
    bge   t0, s6, .L_skip_this_move
    mv    s6, t0              # next_bound = f_score

.L_skip_this_move:
    # 試下一個 move: stack[depth].move_idx++
    lw    t0, 8(s7)
    addi  t0, t0, 1
    sw    t0, 8(s7)
    j     .L_dfs_loop

.L_push_next_depth:
    # 推進到下一層 (depth + 1)
    addi  s5, s5, 1
    slli  t0, s5, 4
    add   t1, sp, t0          # &stack[depth + 1]
    sh    t5, 0(t1)           # np
    sh    t6, 2(t1)           # no
    sw    s10, 4(t1)          # prev_face = face
    sw    x0, 8(t1)           # move_idx = 0
    j     .L_dfs_loop

.L_dfs_end:
    mv    s4, s6              # bound = next_bound
    j     .L_outer_bound_loop

.L_search_success:
    mv    a0, s5              # 回傳解出步數 depth
    j     .L_solve_exit

.L_search_failed:
    li    a0, -1

.L_solve_exit:
    lw    ra, 252(sp)
    lw    s0, 248(sp)
    lw    s1, 244(sp)
    lw    s2, 240(sp)
    lw    s3, 236(sp)
    lw    s4, 232(sp)
    lw    s5, 228(sp)
    lw    s6, 224(sp)
    lw    s7, 220(sp)
    lw    s8, 216(sp)
    addi  sp, sp, 256
    ret

# ==============================================================================
# Main 進入點
# 測試測資 21345671111111 (對應 rank_p = 720, rank_o = 0)
# ==============================================================================
main:
    addi  sp, sp, -16
    sw    ra, 12(sp)

    # 載入極限狀態 rank: p = 720, o = 0
    li    a0, 720
    li    a1, 0
    jal   ra, solve_ida

    # a0 儲存回傳步數 (最佳解應為 11)
    lw    ra, 12(sp)
    addi  sp, sp, 16
    ret
