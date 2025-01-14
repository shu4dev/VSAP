theory Helper
  imports Main
begin

(*----------------------------------------------------------------------------*)
(* 1. Utility functions: getn and restn                                       *)
(*   - getn lst n   = first n elements of lst (or fewer if lst is too short)  *)
(*   - restn lst n  = drop the first n elements of lst                        *)
(*----------------------------------------------------------------------------*)

fun getn :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "getn _ 0 = []"
| "getn [] _ = []"
| "getn (x # xs) (Suc n) = x # getn xs n"

fun restn :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "restn xs 0 = xs"
| "restn [] _ = []"
| "restn (x # xs) (Suc n) = restn xs n"

(*----------------------------------------------------------------------------*)
(* 2. bytes64 : interpret the first 8 bytes of a list as a 64-bit (nat) value *)
(*   - Follows the OCaml logic: we grab 8 bytes, reverse them (so the         *)
(*     last byte in that slice is the least significant), and accumulate      *)
(*     them with base 256.                                                   *)
(*----------------------------------------------------------------------------*)

definition bytes64 :: "int list \<Rightarrow> nat" where
  "bytes64 xs =
     (let first8 = getn xs 8;
          rev8   = rev first8
      in foldl (\<lambda>acc b. acc * 256 + nat b) 0 rev8)"

(*----------------------------------------------------------------------------*)
(* 3. n64bytes : produce exactly 8 bytes (as ints) encoding a nat in base 256 *)
(*   - We replicate the OCaml code: make_rev_bytes constructs bytes from the  *)
(*     least significant portion up, then we reverse to get the final list.   *)
(*----------------------------------------------------------------------------*)

fun make_rev_bytes :: "nat \<Rightarrow> nat \<Rightarrow> int list" where
  "make_rev_bytes _ 0 = []"
| "make_rev_bytes n (Suc i) =
     (let b  = int (n mod 256);
          n' = n div 256
      in b # make_rev_bytes n' i)"

definition n64bytes :: "nat \<Rightarrow> int list" where
  "n64bytes n = rev (make_rev_bytes n 8)"

(*----------------------------------------------------------------------------*)
(* 4. split_name : split a list at the first 0 byte, keeping that 0 in the    *)
(*   “name” portion. Mirrors the OCaml function 'separate_name'.             *)
(*----------------------------------------------------------------------------*)

fun split_name :: "int list \<Rightarrow> (int list \<times> int list)" where
  "split_name [] = ([], [])"
| "split_name (x # xs) = (
     if x = 0 then
       ([0], xs)
     else
       let (nm_end, leftover) = split_name xs
       in (x # nm_end, leftover)
   )"
end