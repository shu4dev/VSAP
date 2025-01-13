theory imperative_concrete
  imports Main abstract
begin

(****************************************************************************)
(* 1. Low-level representation of device state                              *)
(****************************************************************************)

type_synonym Byte  = nat
type_synonym Block = "Byte list"
  (* Each block is a list of bytes (similar to the OCaml “int list”). *)
  
record ConcreteFS_State = 
  blocks     :: "Block list"   (* low-level storage: list of blocks *)
  block_size :: nat            (* size in bytes of each block *)
  nb         :: nat            (* number of blocks *)


(****************************************************************************)
(* 2. Helper functions for blocks & file metadata                           *)
(****************************************************************************)

(* For simplicity, we store each “file” in exactly one block in this model. 
   Realistically, you'd replicate your SASFS multi-block approach here. *)

definition block_is_empty :: "Block \<Rightarrow> bool" where
  "block_is_empty blk \<equiv> (blk = [])"

definition block_filename :: "Block \<Rightarrow> string" where
  "block_filename blk \<equiv> 
     (if length blk < 2 then ''''  (* no valid filename if too short *)
      else let name_len = hd blk 
           in String.implode (map char_of_nat (take name_len (tl blk))))"

definition block_content :: "Block \<Rightarrow> Content" where
  "block_content blk \<equiv> 
     (if length blk < 2 then [] 
      else let name_len = hd blk
           in drop (Suc name_len) blk )"


(****************************************************************************)
(* 3. Concrete operations: new_file, read_file, delete_file                 *)
(****************************************************************************)

(* new_file_concrete tries to create a new file [f] with content [c].
   We store it in the first empty block we find, if any. 
   - The block format: 
       [name_len, <name bytes>, ...content...]
     so the first byte is the length of the filename, 
     then that many bytes for the name, then the file content. *)

fun new_file_concrete :: "ConcreteFS_State \<Rightarrow> string \<Rightarrow> Content \<Rightarrow> ConcreteFS_State option" where
  "new_file_concrete s f c = (
     let fname_len = length f;
         bs       = block_size s;
         nblocks  = nb s;
         blk_data = (fname_len # map nat_of_char (String.explode f)) @ c
     in if fname_len = 0 \<or> fname_len + length c + 1 > bs 

        then None  (* file name too large or something else *)
        else 

          (let old_blocks = blocks s in
           case find_index (\<lambda>blk. block_is_empty blk) old_blocks of
             None       \<Rightarrow> None
           | Some idx   \<Rightarrow> 
               let new_blk = blk_data
                   ; new_blocks = old_blocks[idx := new_blk]
                   in Some (s\<open>blocks := new_blocks\<close>)))"

(* read_file_concrete simply scans all blocks to find a match by filename. 
   If found, return Some content; else None. *)

fun read_file_concrete :: "ConcreteFS_State \<Rightarrow> string \<Rightarrow> Content option" where
  "read_file_concrete s f = (
     let bs = blocks s in
     case find (\<lambda>blk. block_filename blk = f) bs of
       None     \<Rightarrow> None
     | Some blk \<Rightarrow> Some (block_content blk))"

(* delete_file_concrete scans blocks, if a file with name [f] is found,
   overwrite that block with [] (empty). *)

fun delete_file_concrete :: "ConcreteFS_State \<Rightarrow> string \<Rightarrow> ConcreteFS_State" where
  "delete_file_concrete s f = (
     let bs = blocks s in
     case find_index (\<lambda>blk. block_filename blk = f) bs of
       None     \<Rightarrow> s  (* file not found, do nothing *)
     | Some idx \<Rightarrow> 
         let new_bs = bs[idx := []] 
         in s\<open>blocks := new_bs\<close> )"


(****************************************************************************)
(* 4. Abstraction function \<alpha>: ConcreteFS_State \<Rightarrow> FS_State (Filename \<Rightarrow> Content option) *)
(****************************************************************************)

type_synonym FS_State = "string \<Rightarrow> Content option"

definition \<alpha> :: "ConcreteFS_State \<Rightarrow> FS_State" where
  "\<alpha> s \<equiv> (\<lambda>f. 
    let possible_blk = find (\<lambda>blk. block_filename blk = f) (blocks s)
    in case possible_blk of
         None       \<Rightarrow> None
       | Some blk   \<Rightarrow> Some (block_content blk))"

(****************************************************************************)
(* 5. Examples of refinement statements                                     *)
(****************************************************************************)

(* For example, we want to show that if [new_file_concrete] in the concrete model 
   returns Some s', then [new_file_abs (\<alpha> s) f c] = Some (\<alpha> s'). 

   The abstract operations you had are:
     new_file_abs fs f c = (if fs f = None then Some (fs(f := Some c)) else None)
   So we want:
     if new_file_concrete s f c = Some s' then
       new_file_abs (\<alpha> s) f c = Some (\<alpha> s').

   A skeleton of such a lemma is below:
*)

lemma new_file_refinement:
  assumes "new_file_concrete s f c = Some s'"
  shows   "new_file_abs (\<alpha> s) f c = Some (\<alpha> s')"
proof -
  (* Proof outline:
     1. Expand new_file_concrete's definition, get the conditions under 
        which it returns Some s'.
     2. Identify which block got updated from [] to the new file data.
     3. Show in the abstract view, that means the file didn't previously exist 
        (i.e., (\<alpha> s) f = None), and now it is (Some c).
     4. Therefore new_file_abs (\<alpha> s) f c = Some (\<alpha> s'), 
        with \<alpha> s' reflecting exactly that new file. 
  *)
  sorry
qed

(* Similarly, you can prove refinement lemmas for read_file and delete_file 
   to match read_file_abs and delete_file_abs. *)

end