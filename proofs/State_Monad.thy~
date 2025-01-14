theory State_Monad
  imports Main "HOL-Library.Monad_Syntax"
begin

type_synonym ('a, 's) s_monad = "'s \<Rightarrow> (('a \<times> 's) option)"

definition return :: "'a \<Rightarrow> ('a, 's) s_monad" where
  "return x \<equiv> (\<lambda>s. Some (x, s))"

definition bind ::
  "('a, 's) s_monad \<Rightarrow> ('a \<Rightarrow> ('b, 's) s_monad) \<Rightarrow> ('b, 's) s_monad"
    (infixl ">>=" 60) where
  "bind f g \<equiv> (\<lambda>s. case f s of
                    None \<Rightarrow> None
                  | Some (x, s') \<Rightarrow> g x s')"



translations
  "do { x \<leftarrow> f; rest }" == "bind f (\<lambda>x. do { rest })"
  "do { return e }"    == "return e"

abbreviation (input) fail :: "('a, 's) s_monad" where
  "fail \<equiv> (\<lambda>_. None)"

end