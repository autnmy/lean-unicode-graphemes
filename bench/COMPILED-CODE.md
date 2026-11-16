# What the compiled benchmark runs on each timed call

This record reads the C that Lean generates for the benchmark's timed calls. It checks the
README's Timing claim: "This library's time includes copying each cluster into a new `String`;
UnicodeExtra's covers its slices." The source only shows what the code asks for. The compiler
can drop or hoist work whose result looks unused, and the timed calls use only a count. So the
generated C is the evidence for what each timed call does.

**What was read.** The C comes from one build of `bench/` with `leanprover/lean4:v4.35.0`, the
toolchain in `bench/lean-toolchain`. The source is the tree of the commit that adds this file.
The record does not cover any other toolchain or source. It does not cover the published Results
table in the README either: that table came from run 43705448890 on
`leanprover/lean4:v4.36.0-rc2`, whose C nobody read. A toolchain bump or a change to the files
below can change the C, and this record does not update itself. Re-read the C after such a
change before relying on this record.

The files, as Lake writes them, with the SHA-256 of the copies read here:

| File | SHA-256 |
|---|---|
| `bench/.lake/build/ir/Bench/Libraries.c` | `62f9e2653753bfa2b6179e0c306ccca0f7be5ba6fc99a655fc89ea81eb4b36d9` |
| `bench/.lake/build/ir/Bench/Measure.c` | `d5a9e9071802f3561aa030ad1126f866850785df5f0f8c63456f8645c0d9e3dc` |
| `bench/.lake/build/ir/Main.c` | `6a5d460f669579f57ef3c5cd264842477c9986eeb573a511f3a53d5fb8d8a7d5` |
| `.lake/build/ir/Segmentation/Graphemes.c` | `53fb1781af1cf38c4ebf67548bd1c64be94c7edcced6dc4e6b40a1180f23fce7` |

The last file is the library's own module. The bench builds the library by path, so Lake writes
its C into the root package's `.lake/`.

**The run.** Before the C was read, the same build ran the benchmark's own steps in `bench/`.
`sh build.sh results.md` built every target. `lake test` passed its 4 runtime checks.
`lake exe bench check` printed "Both libraries return the same clusters on every input."
`lake exe bench report results.md` timed both libraries on `plain-ascii`, `mixed-scripts`, `emoji`
and `large-mixed` and wrote the table. Those local times are not published. The README's numbers
come only from CI.

Excerpts below are copied from the generated files. `/* ... */` marks lines left out of an
excerpt. Long symbol names are copied whole, because the name is what ties a call to its
definition.

## 1. Each call of `oursClusterCount` segments the text

`lp_bench_Bench_oursClusterCount` (Libraries.c) calls `oursClusters` and counts the list it
returns. It does no other work, and nothing guards the call:

```c
LEAN_EXPORT lean_object* lp_bench_Bench_oursClusterCount(lean_object* v_text_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lp_bench_Bench_oursClusters(v_text_41_);
v___x_43_ = l_List_lengthTR___redArg(v___x_42_);
lean_dec(v___x_42_);
return v___x_43_;
}
}
```

`lp_bench_Bench_oursClusters` (Libraries.c) turns the text into a `List Char` (`lean_string_data`
is `String.toList`). It segments that list with `clustersOf`, then maps the clusters to strings,
on every call, with no branch:

```c
LEAN_EXPORT lean_object* lp_bench_Bench_oursClusters(lean_object* v_text_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_3_ = ((lean_object*)(lp_bench_Bench_oursClusters___closed__0));
v___x_4_ = lean_string_data(v_text_2_);
v___x_5_ = lp_lean_x2dunicode_x2dgraphemes_Segmentation_clustersOf(v___x_3_, v___x_4_);
v___x_6_ = lean_box(0);
v___x_7_ = lp_lean_x2dunicode_x2dgraphemes_List_mapTR_loop___at___00Segmentation_graphemes_spec__0(v___x_5_, v___x_6_);
return v___x_7_;
}
}
```

`clustersOf` is a call into the library's compiled module, not inlined code, so the compiler cannot
skip it here. The call goes to the reference `List Char` path. The `@[csimp]` rewrite to the slice
scanner applies to `Segmentation.graphemes`, and the bench does not call `Segmentation.graphemes`.

## 2. Each cluster is copied into a new `String`

The map loop is `lp_lean_x2dunicode_x2dgraphemes_List_mapTR_loop___at___00Segmentation_graphemes_spec__0`
(Segmentation/Graphemes.c). The bench reuses the library's specialisation of `List.map
String.ofList`, which has the same shape. Each pass takes one cluster (`v_head_466_`) and calls
`lean_string_mk`, the runtime function behind `String.ofList`, on it. The pass then moves to the
tail and jumps back to `_start`. The `lean_is_exclusive` branches only choose whether to reuse the
list cell, and both of them reach the copy:

```c
lean_object* v_head_466_; lean_object* v_tail_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
v_head_466_ = lean_ctor_get(v_a_463_, 0);
v_tail_467_ = lean_ctor_get(v_a_463_, 1);
/* ... both branches of the lean_is_exclusive test end in: goto v_resetjp_468_; */
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_string_mk(v_head_466_);
/* ... the new string is stored in a list cell, reused or freshly allocated,
       and both paths end in: goto v_reusejp_472_; */
v_reusejp_472_:
{
v_a_463_ = v_tail_467_;
v_a_464_ = v___x_473_;
goto _start;
}
```

The loop stops only when the list is empty (`lean_obj_tag(v_a_463_) == 0`). So `lean_string_mk`
runs once for each cluster. The list of new strings is built in full and then counted by
`l_List_lengthTR___redArg` in `oursClusterCount`. The copies are not dropped, even though only
their count is used.

## 3. Each call of `theirsClusterCount` segments the text once, then counts

`lp_bench_Bench_theirsClusterCount` (Libraries.c) builds a slice over the whole text and calls
`Unicode.graphemeClusters` on it, every time. It then counts the array in a loop:

```c
v_count_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_string_utf8_byte_size(v_text_59_);
v___x_62_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_62_, 0, v_text_59_);
lean_ctor_set(v___x_62_, 1, v_count_60_);
lean_ctor_set(v___x_62_, 2, v___x_61_);
v___x_63_ = lp_UnicodeExtra_Unicode_graphemeClusters(v___x_62_);
v_sz_64_ = lean_array_size(v___x_63_);
lean_dec_ref(v___x_63_);
v___x_65_ = ((size_t)0ULL);
v___x_66_ = lp_bench___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Bench_theirsClusterCount_spec__0___redArg(v_sz_64_, v___x_65_, v_count_60_);
return v___x_66_;
```

The counting loop
(`lp_bench___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Bench_theirsClusterCount_spec__0___redArg`)
adds 1 for each index below the array's size and jumps back to `_start`. It never reads or copies a
slice. So UnicodeExtra's time covers segmentation and building its array of slices, with no
copies, as the README says.

Segmentation itself runs inside `Unicode.graphemeClusters`
(`bench/vendor/UnicodeExtra/UnicodeExtra/Grapheme.lean`). That function walks every position of
the slice and pushes a slice at each break. It is a call into UnicodeExtra's compiled module, so it
runs on each call of `theirsClusterCount`. Its own C is UnicodeExtra's code and is not quoted here.

## 4. The timing loop calls the timed function on every pass

The inner loop of `timeSamples`, the one that makes `callsPerSample` calls, is
`lp_bench___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Bench_timeSamples_spec__0___redArg`
(Measure.c). While `i < stop`, each pass does four things in order. It reads the text from its
reference (`lean_st_ref_get`). It applies the timed closure `v_clusterCount_414_` to that text
(`lean_apply_1`). It adds the result to the running total and stores the total back in its
reference. Then it advances `i` and jumps back to `_start`. No branch skips the call:

```c
v___x_421_ = lean_nat_dec_lt(v_i_417_, v_stop_419_);
if (v___x_421_ == 0)
{
/* ... returns: the loop is done */
}
else
{
/* ... */
v___x_423_ = lean_box(0);
v___x_424_ = lean_st_ref_get(v_val_412_);
v___x_425_ = lean_st_ref_take(v_val_413_);
lean_inc_ref(v_clusterCount_414_);
v___x_426_ = lean_apply_1(v_clusterCount_414_, v___x_424_);
v___x_427_ = lean_nat_add(v___x_425_, v___x_426_);
lean_dec(v___x_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_st_ref_put(v_val_413_, v___x_427_);
v___x_429_ = lean_nat_add(v_i_417_, v_step_420_);
lean_dec(v_i_417_);
v_b_416_ = v___x_423_;
v_i_417_ = v___x_429_;
goto _start;
}
```

`lean_apply_1` calls an opaque closure, so the compiler cannot compute it once and reuse the
result. The text is also read fresh from the reference on each pass. The counted-sample loop
(`..._timeSamples_spec__2___redArg`) runs this inner loop once per sample over the range from 0 to
`callsPerSample`, with the clock read on each side:

```c
v___x_486_ = lean_io_mono_nanos_now();
v_callsPerSample_487_ = lean_ctor_get(v_plan_473_, 2);
/* ... v___x_489_ is the range 0 .. callsPerSample, step 1 */
v___x_491_ = lp_bench___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Bench_timeSamples_spec__0___redArg(v_val_474_, v_val_475_, v_clusterCount_476_, v___x_489_, v___x_490_, v___x_485_);
/* ... */
v___x_492_ = lean_io_mono_nanos_now();
v___x_493_ = lean_nat_sub(v___x_492_, v___x_486_);
/* ... */
v___x_494_ = lean_nat_div(v___x_493_, v_callsPerSample_487_);
```

`lp_bench_Bench_timeSamples` creates the two references and passes its own `v_clusterCount_572_`
to the warm-up loop (`..._spec__1___redArg`) and to the counted-sample loop (`..._spec__2___redArg`).
After the loops, it reads the total and prints it with `IO.eprintln`. Because the total is printed,
the calls that produce it are kept. So the `timeSamples` docstring in `bench/Bench/Measure.lean`
matches what this build does.

## 5. The closure that is timed is the one the run asked for

`lp_bench_Bench_clusterCountOf` (Main.c) returns static closures whose function pointer is the
timed function itself. Case 1 returns `some oursClusterCount`, the default case returns
`some theirsClusterCount`, and case 0 (the baseline) returns `none`:

```c
static const lean_closure_object lp_bench_Bench_clusterCountOf___closed__0_value = {/* ... */ .m_fun = (void*)lp_bench_Bench_oursClusterCount, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
/* ... closed__1 is `some` around closed__0 */
static const lean_closure_object lp_bench_Bench_clusterCountOf___closed__2_value = {/* ... */ .m_fun = (void*)lp_bench_Bench_theirsClusterCount, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
/* ... closed__3 is `some` around closed__2 */
```

The child process's entry passes that result straight to `measureChild` (Main.c):

```c
v___x_340_ = lp_bench_Bench_clusterCountOf(v_library_338_);
v___x_341_ = lp_bench_Bench_measureChild(v___x_340_, v_kind_339_);
```

`lp_bench_Bench_measureChild` (Measure.c) unwraps the `some` and passes the closure inside it to
`timeSamples`, unchanged:

```c
v_val_780_ = lean_ctor_get(v_clusterCount_750_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v_clusterCount_750_, 1);
v___x_781_ = lp_bench_Bench_timingPlan(v_kind_751_);
v___x_782_ = lp_bench_Bench_timeSamples(v_val_780_, v_text_770_, v___x_781_);
```

So the closure that `lean_apply_1` calls in section 4 is `lp_bench_Bench_oursClusterCount` or
`lp_bench_Bench_theirsClusterCount`, whose bodies are quoted in sections 1 to 3.

## Conclusion

In this build, every timed call of this library converts the text to a `List Char`, segments it
with `clustersOf`, and copies each cluster into a new `String` with `lean_string_mk`. Every timed
call of UnicodeExtra segments the text with `Unicode.graphemeClusters` and counts the slices
without copying them. The timing loop makes each of those calls on every pass. The README's Timing
sentence holds for this build.
