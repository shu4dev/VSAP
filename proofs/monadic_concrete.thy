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

definition read_blockM :: "nat \<Rightarrow> (int list, device_state) s_monad" where
  "read_blockM bn \<equiv> (\<lambda>dev.
     if bn < nb dev then Some (blocks dev bn, dev) else None)"

definition write_blockM :: "nat \<Rightarrow> int list \<Rightarrow> (unit, device_state) s_monad" where
  "write_blockM bn newdata \<equiv> (\<lambda>dev.
     if bn < nb dev \<and> length newdata = bs dev then
       Some ((), dev\<lparr>blocks := (blocks dev)(bn := newdata)\<rparr>)
     else
       None)"

(******************************************************************************)
(* 3. find_empty in monadic style                                             *)
(******************************************************************************)

definition is_empty_block :: "int list \<Rightarrow> bool" where
  "is_empty_block blk \<equiv>
     (case parse_block blk of
        None \<Rightarrow> True
      | Some fm \<Rightarrow> (length (fname fm) = 1))"

definition find_emptyM :: "nat \<Rightarrow> (nat, device_state) s_monad" where
  "find_emptyM needed_size \<equiv> (\<lambda>dev.
     if needed_size > bs dev then None
     else
       let max_bn = nb dev in
       let scan = (\<lambda>bn.
         if bn = max_bn then None
         else
           case blocks dev bn of
             blk \<Rightarrow> if is_empty_block blk then Some (bn) else scan (bn + 1))
       in (case scan 0 of
            None     \<Rightarrow> None
          | Some bn' \<Rightarrow> Some (bn', dev)))"

(******************************************************************************)
(* 7. new_file in monadic style                                               *)
(******************************************************************************)

definition new_fileM ::
  "string \<Rightarrow> int list \<Rightarrow> (unit, device_state) s_monad"
where
  "new_fileM nm data \<equiv> do {
     dev \<leftarrow> (\<lambda>s. Some (s, s));  \<comment> \<open>equivalent to 'get' in a state monad\<close>

     let name_bytes = map (\<lambda>c. int (Char.ord c)) (String.explode nm) @ [0];
     let needed_size = 8 + length name_bytes + length data;

     _ \<leftarrow> (\<lambda>s'. if needed_size \<le> bs s' 
               then Some ((), s') 
               else None);

     (bn) \<leftarrow> find_emptyM needed_size;

     let fm = \<lparr> fsize = needed_size, fname = name_bytes, fdata = data ⦘;
     let blk = pack_block fm;

     _ \<leftarrow> write_blockM bn blk;

     return ()
   }"

(******************************************************************************)
(* 8. find_file, read_file, delete_file in monadic style                      *)
(******************************************************************************)

definition matches_name :: "file_meta \<Rightarrow> string \<Rightarrow> bool" where
  "matches_name fm s \<equiv>
     let s_bytes = map (\<lambda>c. int (Char.ord c)) (String.explode s) @ [0]
     in fname fm = s_bytes"

(* find_file_loop: purely functional helper that returns Some(bn,fm) if found *)
fun find_file_loop ::
  "device_state \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> (nat * file_meta) option"
where
  "find_file_loop dev s bn =
     (if bn \<ge> nb dev then None
      else
        let blk = blocks dev bn in
        case parse_block blk of
          None \<Rightarrow> find_file_loop dev s (bn + 1)
        | Some fm \<Rightarrow>
            if matches_name fm s then Some (bn, fm)
            else find_file_loop dev s (bn + 1))"

(* find_fileM: monadic wrapper around 'find_file_loop' *)
definition find_fileM ::
  "string \<Rightarrow> ((nat * file_meta), device_state) s_monad"
where
  "find_fileM s \<equiv> (\<lambda>dev.
     case find_file_loop dev s 0 of
       None \<Rightarrow> None
     | Some (bn, fm) \<Rightarrow> Some ((bn, fm), dev))"

text \<open>
  read_fileM:  
   1) find_fileM name  
   2) return the fdata from that file_meta
\<close>
definition read_fileM ::
  "string \<Rightarrow> (int list, device_state) s_monad"
where
  "read_fileM s \<equiv> do {
     (bn, fm) \<leftarrow> find_fileM s;
     return (fdata fm)
   }"

text \<open>
  delete_fileM:  
   1) find_fileM name  
   2) write an empty block or zero block to that block index
\<close>
definition empty_block :: "device_state \<Rightarrow> int list" where
  "empty_block dev \<equiv> replicate (bs dev) 0"

definition delete_fileM ::
  "string \<Rightarrow> (unit, device_state) s_monad"
where
  "delete_fileM s \<equiv> do {
     (bn, fm) \<leftarrow> find_fileM s;
     dev \<leftarrow> (\<lambda>st. Some (st, st));
     let blk0 = empty_block dev;
     _ \<leftarrow> write_blockM bn blk0;
     return ()
   }"
end