# DCache Operation Protocol & Timing

## Cache Access Cycles

### Cycle 0: Request Issue (Combinational)
- **Input**: `cache_req.addr`, `cache_req.valid`
- **Combinational**:
  - `rd_idx = addr[4]` (for 2-set cache, bit 4 is index)
  - Read enables asserted to all arrays (tag, data, dirty, PLRU)
- **Arrays read with rd_idx**: tag_array, data_array, dirty_array, plru_array

### Cycle 1: Hit/Miss Detection & Response
- **Registered inputs available**: All arrays output data from Cycle 0 read
- **Combinational**:
  - Tag comparison: `cache_hit_vec[i] = (tag_array[rd_idx][i] == req_tag) && valid[i]`
  - `cache_hit = |cache_hit_vec`
  - `cache_miss = !cache_hit`
- **Output**:
  - **If HIT**: `cache_res.data = data_array[hit_way][word_offset]`
  - **If MISS**: Start fill/writeback sequence

## Miss Handling Sequence

### Step 1: Determine Eviction (Cycle 1)
- **Inputs** (from Cycle 0 read):
  - `plru_node = plru_array[rd_idx]` (read in Cycle 0)
  - `dirty_bits = dirty_array[rd_idx]` (read in Cycle 0)
  - `tag_victim = tag_array[rd_idx][evict_way]` (read in Cycle 0)
  - `data_victim = data_array[rd_idx][evict_way]` (read in Cycle 0)

- **Combinational**:
  - `evict_way = compute_evict_way(plru_node)` (use PLRU to select victim)
  - `wr_idx = req_addr_q[4]` (use registered request index)
  - `write_back = dirty_bits[evict_way] && valid[evict_way]`

- **Writeback Address**:
  - `wb_addr = {tag_victim, wr_idx, 4'b0}` (line-aligned)
  - **CRITICAL**: Tag comes from array read in Cycle 0!

### Step 2a: Writeback (if dirty)
- **Cycle N**: Issue writeback request
  - `lowx_req.valid = 1`
  - `lowx_req.addr = wb_addr` (latched from Step 1)
  - `lowx_req.rw = 1` (write)
  - `lowx_req.data = data_victim` (latched from Step 1)

- **Cycle N+X**: Writeback response
  - `lowx_res.valid = 1`
  - **Action**: Clear dirty bit ONLY
    - `dirty_array[wr_idx][evict_way] = 0`
  - **DO NOT** update PLRU (evict_way must stay same!)

### Step 2b: Fill Request
- **After writeback (or immediately if clean)**:
  - `lowx_req.valid = 1`
  - `lowx_req.addr = req_addr_q` (original miss address, line-aligned)
  - `lowx_req.rw = req_rw_q` (original request type)
  - `lowx_req.data = req_data_q` (if write)

### Step 3: Fill Response & Array Update
- **Cycle M**: Fill response arrives
  - `lowx_res.valid = 1`
  - `lowx_res.data = fill_data`

- **Actions** (all in same cycle):
  1. **Write Tag Array**:
     - `tag_array[wr_idx][evict_way] = {1'b1, req_tag_q}`
     - Valid bit set to 1

  2. **Write Data Array**:
     - `data_array[wr_idx][evict_way] = fill_data`

  3. **Set Dirty Bit** (if write request):
     - `dirty_array[wr_idx][evict_way] = req_rw_q`

  4. **Update PLRU**:
     - `plru_array[wr_idx] = update_plru(plru_old, evict_way)`
     - Mark evict_way as MRU (most recently used)

## Hit Path (Write)

### Cycle 0: Request
- Same as read

### Cycle 1: Hit Detection & Write
- **If HIT**:
  1. **Write Data Array**:
     - `data_array[rd_idx][hit_way][byte_offset] = write_data`
     - Byte-enable based on rw_size

  2. **Set Dirty Bit**:
     - `dirty_array[rd_idx][hit_way] = 1`

  3. **Update PLRU**:
     - `plru_array[rd_idx] = update_plru(plru_old, hit_way)`

## Critical Invariants

### Array Consistency
1. **Valid implies tag is meaningful**: `valid[i] == 1 → tag[i] is valid`
2. **Dirty implies valid**: `dirty[i] == 1 → valid[i] == 1`
3. **PLRU points to LRU way**: After access to way X, PLRU should point away from X

### Writeback Rules
1. **Writeback address formation**: MUST use tag read from array in miss detection cycle
2. **Evict way stability**: evict_way MUST NOT change during writeback sequence
3. **PLRU freeze**: PLRU MUST NOT update during writeback (only during fill)
4. **Dirty bit timing**: Clear dirty ONLY when writeback response arrives

### Latch Requirements
During miss handling, these MUST be latched and held stable:
- `req_addr_q`
- `req_tag_q`
- `req_rw_q`
- `req_data_q`
- `evict_way_q` ← **CRITICAL! Must not change!**
- `evict_tag_q` ← **CRITICAL! From array read, not recomputed!**
- `evict_data_q` ← **CRITICAL! From array read!**
- `wr_idx_q`

## Test Requirements

### Functional Tests
1. **Cold Miss**: Empty cache, all accesses should miss
2. **Hit After Fill**: Re-access same address, should hit
3. **Capacity Miss**: Fill all ways, next access should evict
4. **Dirty Eviction**: Write then evict, should see writeback
5. **Tag Aliasing**: Different tags, same index, should miss

### Backdoor Checks
After each operation, verify:
1. **Tag Array**: Correct tag written at correct index/way
2. **Data Array**: Correct data written
3. **Dirty Array**: Correct state (set on write, clear on writeback)
4. **PLRU Array**: Updated correctly (point to LRU after access)
5. **Valid Bits**: Set on fill, maintain correctly

### Timing Checks
1. **Array Read Timing**: Data available in cycle after request
2. **Hit Response Timing**: Valid in same cycle as hit detection
3. **Miss Latency**: Fill response after N memory cycles
4. **Writeback Priority**: Writeback completes before fill

## Known Bugs (from earlier analysis)

### Bug 1: evict_way not latched
- **Symptom**: evict_way changes during writeback
- **Fix**: Latch evict_way when miss detected, use latched value

### Bug 2: evict_tag/data not latched
- **Symptom**: Writeback address = 0x0, wrong data
- **Fix**: Latch tag/data from array read in miss cycle

### Bug 3: PLRU updates during writeback
- **Symptom**: evict_way changes unexpectedly
- **Fix**: Only update PLRU during fill, not writeback

### Bug 4: Testbench timing
- **Symptom**: Data sampled after cache_res goes invalid
- **Fix**: Sample immediately when cache_res.valid asserts
