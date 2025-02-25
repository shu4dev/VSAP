theory abstract
  imports Main
begin

type_synonym Byte = nat
type_synonym Content = "Byte list"
type_synonym Filename = string
type_synonym FS_State = "Filename \<Rightarrow> Content option"

definition new_file_abs :: "FS_State \<Rightarrow> Filename \<Rightarrow> Content \<Rightarrow> FS_State option" where
 "new_file_abs fs f c = (if fs f = None then Some (fs(f := Some c)) else None)"

definition read_file_abs :: "FS_State \<Rightarrow> Filename \<Rightarrow> Content option" where
 "read_file_abs fs f = fs f"

definition delete_file_abs :: "FS_State \<Rightarrow> Filename \<Rightarrow> FS_State option" where
 "delete_file_abs fs f = (if fs f \<noteq> None then Some (fs(f := None)) else None)"

(*-------------------------------------------------------*)
lemma read_after_create_abstract:
  assumes "new_file_abs fs f c = Some fs'"
  shows "read_file_abs fs' f = Some c"
  using assms
  unfolding new_file_abs_def read_file_abs_def
  by (metis map_upd_Some_unfold option.distinct(1))

datatype FS_Op = New Filename Content | Read Filename | Delete Filename

fun apply_op :: "FS_State \<Rightarrow> FS_Op \<Rightarrow> FS_State option" where
  "apply_op fs (New f c)    = new_file_abs fs f c"
| "apply_op fs (Read f)     = Some fs"
| "apply_op fs (Delete f)   = delete_file_abs fs f"

fun apply_ops :: "FS_State \<Rightarrow> FS_Op list \<Rightarrow> FS_State option" where
  "apply_ops fs []       = (if fs = (\<lambda>x. None) then None else Some fs)"
| "apply_ops fs (op#ops) =
     (case apply_op fs op of
        None      \<Rightarrow> apply_ops fs ops 
      | Some fs'  \<Rightarrow> apply_ops fs' ops)"

(* Helper lemma for New: if a new_file_abs succeeds for some f' \<noteq> f, then f is not changed *)
lemma new_does_not_delete_other_file:
  assumes "new_file_abs fs f' c = Some fs1" and "f \<noteq> f'"
  shows "fs1 f = fs f"
  using assms
  unfolding new_file_abs_def
  by (metis fun_upd_other option.distinct(1) option.inject)

(* Helper lemma for Delete: if delete_file_abs succeeds for some f' \<noteq> f, then f is not changed *)
lemma delete_does_not_affect_other_file:
  assumes "delete_file_abs fs f' = Some fs1" and "f \<noteq> f'"
  shows "fs1 f = fs f"
  using assms
  unfolding delete_file_abs_def
  by (metis fun_upd_other option.distinct(1) option.inject)

(*-------------------------------------------------------*)
lemma preserve_file_presence:
  assumes "apply_ops fs ops = Some fs'"
    and "f \<notin> {f'. (Delete f') \<in> set ops}"
    and "f \<notin> {f'. (New f' c) \<in> set ops}"
  shows "fs f = fs' f"
  using assms
proof (induct ops arbitrary: fs)
  case Nil
  then show ?case 
  proof (cases "fs = (\<lambda>x. None)")
    case True
    then have "apply_ops fs [] = None" by simp
    hence "None = Some fs'" using Nil by simp
    then show ?thesis by simp
  next
    case False
    then have "apply_ops fs [] = Some fs" by simp
    hence "Some fs = Some fs'" using Nil by simp
    then have "fs = fs'" using option.inject by simp
    then show ?thesis by simp
  qed
next
  case (Cons a ops)
  then show ?case 
  proof (cases a)
    case (New f' c)
    have "apply_op fs (New f' c) = new_file_abs fs f' c" by simp
    then show ?thesis
      unfolding new_file_abs_def
      apply simp
      apply (simp add: new_does_not_delete_other_file)
  next
    case (Read f')
    then show ?thesis sorry
  next
    case (Delete f')
    then show ?thesis sorry
  qed
qed

end
