theory monadic_concrete
 imports Main
begin

text \<open>
  We'll assume each block is a list of bytes (nat), and the device is
  a record containing (1) block size, (2) number of blocks, and
  (3) a list of blocks.
\<close>

type_synonym byte = nat
type_synonym block = "byte list"

record device_state =
  bs :: nat
  nb :: nat
  blocks :: "block list"

text \<open>
  We want an invariant that:
    - length(blocks dev) = nb dev
    - each block has length bs dev
  We'll skip formalizing it here, but typically you'd define:
      invariant dev \<equiv> length(blocks dev) = nb dev
                     \<and> (\<forall> blk \<in> set(blocks dev). length blk = bs dev)
\<close>

(* For returning either an updated device or an error message. *)
datatype ('state, 'err, 'val) FSResult =
    Ok "'state" "'val"
  | Err "'err"

text \<open>
  We'll define a helper monad-like operator for chaining results.
  This is NOT the standard Isabelle State-Monad library, just a sketch.
\<close>

definition bind :: "('state, 'err, 'val) FSResult \<Rightarrow> ('val \<Rightarrow> ('state, 'err, 'val2) FSResult) \<Rightarrow> ('state, 'err, 'val2) FSResult" where
"bind r f = (case r of
   Err e      \<Rightarrow> Err e
 | Ok st val  \<Rightarrow> f val)"

syntax
  "_bind" :: "[logic, pttrn, logic] \<Rightarrow> logic"  ("do_option { _ \<bind> (_ \<rightarrow>) _ }")
translations
  "do_option { X \<bind> (v \<rightarrow>) Y }" \<rightleftharpoons>
    "CONST bind X (\<lambda> v. Y)"

abbreviation ret :: "'state \<Rightarrow> 'val \<Rightarrow> ('state, 'err, 'val) FSResult" ("return _ _")
  where "return st v \<equiv> Ok st v"

abbreviation err :: "'err \<Rightarrow> ('state, 'err, 'val) FSResult" ("fail _")
  where "fail e \<equiv> Err e"

text \<open>
  Now let's define read/write in a purely functional style. We pass in
  the device_state and return a new device_state (unchanged or updated)
  plus the result (the block read, or unit, etc.).
\<close>

definition read_block :: "device_state => nat => (device_state, string, block) FSResult" where
"read_block dev b = (if b < nb dev then return dev ((blocks dev)!b) else fail ''block index out of range'')"

definition write_block ::
  "device_state \<Rightarrow> nat \<Rightarrow> block \<Rightarrow> (device_state, string, unit) FSResult"
where
"write_block dev b newblk =
   (if b < nb dev then
      if length newblk = bs dev then
        let new_blocks = (blocks dev)[b := newblk] in
        let dev' = dev \<lparr> blocks := new_blocks \<rparr> in
        return dev' ()
      else fail ''wrong block size''
    else fail ''block index out of range'')"

text \<open>
  Sample: format the device by zeroing out all blocks. We'll do
  a fold from 0 to nb-1. If at any step there's an error, we stop.
\<close>

definition format_conc ::
  "device_state \<Rightarrow> (device_state, string, unit) FSResult"
where
"format_conc dev =
   (if bs dev \<le> 9
    then fail ''bs too small''
    else
      let zero_blk = replicate (bs dev) 0 in
      let nblocks = nb dev in
      let result =
         fold (\<lambda> i r. do_option {
                 r \<bind> (st' \<rightarrow>)
                 write_block st' i zero_blk
               })
              [0..<nblocks]
              (return dev ())
      in
      case result of
        Err e \<Rightarrow> Err e
      | Ok st' _ \<Rightarrow> return st' ()))"

text \<open>
  We'll not define the entire new_file, read_file, etc. here, but they'd follow
  the same pattern: do an operation, if success, pass the updated dev to the next,
  otherwise fail. Then return the final dev + some result.
\<close>

end