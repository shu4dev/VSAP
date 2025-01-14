theory monadic_concrete
 imports Main Helper State_Monad
begin

(****************************************************************************)
(* 1. Low-level representation of device state and file metadata            *)
(****************************************************************************)

record device_state =
  dev_name :: string
  bs       :: nat
  nb       :: nat
  blocks   :: "nat \<Rightarrow> int list"

record file_meta =
  fsize :: nat
  fname :: "int list"
  fdata :: "int list"

definition parse_block :: "int list \<Rightarrow> file_meta option" where
  "parse_block blk \<equiv>
     (if length blk < 8 then None
      else
        let sz       = bytes64 blk;
            leftover = restn blk 8;
            (nm, rest) = split_name leftover;
            used = 8 + length nm + length rest
        in if used \<le> length blk \<and> sz = used
           then Some (\<lparr>fsize = sz, fname = nm, fdata = rest\<rparr>)
           else None)"

definition pack_block :: "file_meta \<Rightarrow> int list" where
  "pack_block fm \<equiv>
     n64bytes (fsize fm) @ fname fm @ fdata fm"

(******************************************************************************)
(* 2. Monadic read_block / write_block                                        *)
(******************************************************************************)

definition read_blockM :: "nat \<Rightarrow> (device_state, int list) nondet_monad" where
  "read_blockM bn \<equiv> do {
     s \<leftarrow> get;
     guard (\<lambda>_. bn < nb s);
     return (blocks s bn)
   }"

definition write_blockM ::
  "nat \<Rightarrow> int list \<Rightarrow> (device_state, unit) nondet_monad"
where
  "write_blockM bn newdata \<equiv> do {
     s \<leftarrow> get;
     guard (\<lambda>_. bn < nb s \<and> length newdata = bs s);
     put (s \<lparr> blocks := (blocks s)(bn := newdata) \<rparr>)
   }"

(******************************************************************************)
(* 3. find_empty in monadic style                                             *)
(******************************************************************************)

definition is_empty_block :: "int list \<Rightarrow> bool" where
  "is_empty_block blk \<equiv>
     (case parse_block blk of
        None     \<Rightarrow> True              
      | Some fm  \<Rightarrow> (length (fname fm) = 1))"

definition find_emptyM :: "nat \<Rightarrow> (device_state, nat) nondet_monad" where
  "find_emptyM needed_size \<equiv> do {
     s \<leftarrow> get;
     guard (\<lambda>_. needed_size \<le> bs s);
     let empties = {bn. bn < nb s \<and> is_empty_block (blocks s bn)};
     bn \<leftarrow> select empties;       
     return bn
   }"

(******************************************************************************)
(* 7. new_file in monadic style                                               *)
(******************************************************************************)

definition char_to_nat :: "char \<Rightarrow> int" where
  "char_to_nat c = of_char c"

definition name_to_list :: "String.literal \<Rightarrow> int list" where
  "name_to_list lname = (map char_to_nat (String.explode lname)) @ [0]"

definition new_fileM ::
  "String.literal \<Rightarrow> int list \<Rightarrow> (device_state, unit) nondet_monad"
where
  "new_fileM name data \<equiv> do {
     s \<leftarrow> get;
     let name_bytes  = name_to_list name;
     let needed_size = 8 + length name_bytes + length data;
     guard (\<lambda>_. needed_size \<le> bs s);
     bn \<leftarrow> find_emptyM needed_size;
     let fm  = \<lparr> fsize = needed_size, fname = name_bytes, fdata = data \<rparr>;
     let blk = pack_block fm;
     _ \<leftarrow> write_blockM bn blk;
     return ()
   }"

(******************************************************************************)
(* 8. find_file, read_file, delete_file in monadic style                      *)
(******************************************************************************)

definition matches_name :: "file_meta \<Rightarrow> String.literal \<Rightarrow> bool" where
  "matches_name fm s \<equiv>
     let s_bytes = name_to_list s
     in fname fm = s_bytes"

fun all_file_matches :: "device_state \<Rightarrow> String.literal \<Rightarrow> (nat \<times> file_meta) set" where
  "all_file_matches dev s =
     (if nb dev = 0 then {}
      else
        (\<Union> bn \<in> {0..< nb dev}.
           case parse_block (blocks dev bn) of
             None     \<Rightarrow> {}
           | Some fm \<Rightarrow> if matches_name fm s then {(bn, fm)} else {}))"

definition find_fileM ::
  "String.literal \<Rightarrow> (device_state, (nat \<times> file_meta)) nondet_monad"
where
  "find_fileM s \<equiv> do {
     dev \<leftarrow> get;
     let matches = all_file_matches dev s; 
     (bn, fm) \<leftarrow> select matches;     
     return (bn, fm)
   }"

definition read_fileM :: "String.literal \<Rightarrow> (device_state, int list) nondet_monad" where
  "read_fileM s \<equiv> do {
     (bn, fm) \<leftarrow> find_fileM s;
     return (fdata fm)
   }"

definition empty_block :: "device_state \<Rightarrow> int list" where
  "empty_block dev \<equiv> replicate (bs dev) 0"

definition delete_fileM :: "String.literal \<Rightarrow> (device_state, unit) nondet_monad" where
  "delete_fileM s \<equiv> do {
     (bn, fm) \<leftarrow> find_fileM s;
     d \<leftarrow> get;
     _ \<leftarrow> write_blockM bn (empty_block d);
     return ()
   }"
end