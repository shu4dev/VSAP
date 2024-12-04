theory sap
  imports Main "HOL-Library.Word" "HOL-Library.Option_ord"
begin

record absfile =
  size :: nat
  name :: string
  data :: "nat list"  (* List of bytes *)

(* A well-formed file: the size includes the size of name and data *)
definition well_formed_file :: "absfile \<Rightarrow> bool" where
  "well_formed_file f \<equiv> (size f = length (name f) + length (data f) + 8)"

definition create_file :: "string \<Rightarrow> nat list \<Rightarrow> absfile" where
  "create_file fname fdata = \<lparr>size = length fname + length fdata + 8, name = fname, data = fdata\<rparr>"

definition read_file :: "string \<Rightarrow> absfile list \<Rightarrow> absfile option" where
  "read_file fname flist = (find (\<lambda>f. name f = fname) flist)"

definition delete_file :: "string \<Rightarrow> absfile list \<Rightarrow> absfile list" where
  "delete_file fname flist \<equiv> filter (\<lambda>f. name f \<noteq> fname) flist"

definition unique_file_names :: "absfile list \<Rightarrow> bool" where
  "unique_file_names flist \<equiv> distinct (map name flist)"

definition file_exists :: "string \<Rightarrow> absfile list \<Rightarrow> bool" where
  "file_exists fname flist \<equiv> \<exists>f \<in> set flist. name f = fname"

theorem create_file_in_list: "\<not>file_exists fname flist \<Longrightarrow> file_exists fname (create_file fname fdata # flist)"
  by (auto simp: create_file_def file_exists_def)

theorem delete_file_not_in_list: "file_exists fname flist \<Longrightarrow> \<not>file_exists fname (delete_file fname flist)"
  by (auto simp: delete_file_def file_exists_def)

(* Device type definition *)
record device =
  name :: string
  bs :: "64 word"  (* block size *)
  nb :: "64 word"  (* number of blocks *)
  r :: "64 word \<Rightarrow> nat list"  (* read function *)
  w :: "64 word \<Rightarrow> nat list \<Rightarrow> unit"  (* write function *)

(* Type definitions for file system structures *)
type_synonym byte = nat
type_synonym block = "byte list"
type_synonym filename = string

(* Core invariants as locale assumptions *)
locale filesystem_invariants =
  fixes dev :: device
  assumes bs_positive: "dev.bs > 9"
  and name_size: "\<forall>name. length name \<le> unat dev.bs - 9"
  and block_size: "\<forall>bn. length (dev.r bn) = unat dev.bs"

(* Helper functions *)
fun getn :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "getn [] n = []"
| "getn (x#xs) 0 = []"
| "getn (x#xs) n = x # getn xs (n-1)"

fun restn :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "restn [] n = []"
| "restn xs 0 = xs"
| "restn (x#xs) n = restn xs (n-1)"

(* Converting between 64-bit words and byte lists *)
fun make_rev_bytes :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word list" where
  "make_rev_bytes _ 0 = []"
| "make_rev_bytes x index = (x mod 256) # make_rev_bytes (x div 256) (index - 1)"

definition n64bytes :: "64 word \<Rightarrow> 64 word list" where
  "n64bytes n = rev (make_rev_bytes n 8)"


fun compute :: "nat list \<Rightarrow> nat" where
  "compute [] = 0"
| "compute (first # rest) = 
     (if 0 \<le> first \<and> first < 256 then 
        first + 256 * compute rest 
      else 
        0)" (* Adding a condition check for byte bounds *)

definition bytes64 :: "nat list \<Rightarrow> nat" where
  "bytes64 lst = compute (rev (getn lst 8))"


fun make_zeros :: "nat \<Rightarrow> 64 word list" where
  "make_zeros n = (if n \<le> 0 then [] else 0 # make_zeros (n - 1))"


definition concat :: "64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list" where
 "concat l1 l2  \<equiv> l1 @ l2"

definition make_empty_bytes :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word list" where
  "make_empty_bytes device nb \<equiv> \<lparr> n64bytes nb) @ (make_zeros (device.bs - 8) \<rparr>"

definition make_empty_block :: "device \<Rightarrow> nat \<Rightarrow> nat list" where
  "make_empty_block device nb \<equiv> make_empty_bytes device (nb * device.bs)"


end