theory week09B_demo_gcd_sol
imports WhileLoopRule "HOL-Eisbach.Eisbach"
begin

definition gcd' :: "nat \<Rightarrow> nat \<Rightarrow> ('s,nat) nondet_monad" where
  "gcd' a b \<equiv>
   do {
      (a, b) \<leftarrow> whileLoop (\<lambda>(a, b) b. 0 < a)
                          (\<lambda>(a, b). return (b mod a, a))
                          (a, b);
      return b
   }"

lemma prod_case_wp:
  assumes "\<lbrace>P\<rbrace> f (fst x) (snd x) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> case x of (a,b) \<Rightarrow> f a b \<lbrace>Q\<rbrace>"
  using assms
  apply(auto simp: valid_def split: prod.splits)
  done

lemma gcd'_correct: 
  "\<lbrace>\<lambda>_. True\<rbrace> gcd' x y \<lbrace>\<lambda>r s. r = gcd x y\<rbrace>"
  unfolding gcd'_def
  apply (rule bind_wp)
   apply (rule prod_case_wp)
   apply (rule return_wp)
  apply (rule hoare_weaken_pre)
   apply (rule_tac I="\<lambda>(a,b) s. gcd x y = gcd a b" in whileLoop_wp)
    apply (rule prod_case_wp)
    apply (rule hoare_weaken_pre, rule return_wp)
    apply clarsimp
    find_theorems gcd "_ mod _"
    find_theorems "gcd ?a ?b = gcd ?b ?a"
    apply (simp add: gcd.commute flip: gcd_red_nat)
   apply clarsimp
  apply clarsimp
  done

(* Same, but more automated:
   AutoCorres provides a similar proof method "wp" that you are allowed to use in assignment 3. *)

lemmas wp_thms = bind_wp return_wp prod_case_wp
method wp = (rule hoare_weaken_pre, (rule wp_thms)+)[1]

lemma gcd'_correct2: 
  "\<lbrace>\<lambda>_. True\<rbrace> gcd' x y \<lbrace>\<lambda>r s. r = gcd x y\<rbrace>"
  unfolding gcd'_def
  apply wp
   apply (rule whileLoop_wp[where I="\<lambda>(a,b) s. gcd x y = gcd a b"])
    apply wp
    apply clarsimp
    apply (metis gcd.commute gcd_red_nat)
   apply clarsimp
  apply clarsimp
  done

end
