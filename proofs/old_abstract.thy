theory old_abstract
  imports Main
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
end