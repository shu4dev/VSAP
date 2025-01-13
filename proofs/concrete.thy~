theory concrete
  imports Main
begin

(* Device type definition *)
record device =
  name :: String.literal
  bs :: "nat"  (* block size *)
  nb :: "nat"  (* number of blocks *)
  r :: "nat \<Rightarrow> nat list"  (* read function *)
  w :: "nat \<Rightarrow> nat list \<Rightarrow> unit"  (* write function *)

(* Helper functions *)
fun getn :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "getn [] n = []"
| "getn (x#xs) 0 = []"
| "getn (x#xs) n = x # getn xs (n-1)"

fun restn :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "restn [] n = []"
| "restn xs 0 = xs"
| "restn (x#xs) n = restn xs (n-1)"

fun make_rev_bytes :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "make_rev_bytes n index = (if n = 0 then replicate index 0
                              else  n mod 256 # make_rev_bytes (n div 256) (index - 1))"

definition n64bytes :: "nat \<Rightarrow> nat list" where
  "n64bytes n = rev (make_rev_bytes n 8)"

fun bytes64 :: "nat list \<Rightarrow> nat" where
  "bytes64 [] = 0"
| "bytes64 xs = foldl (\<lambda>acc x. acc * 256 + x) 0 xs"

fun make_zeros :: "nat \<Rightarrow> nat list" where
  "make_zeros 0 = []"
| "make_zeros n = 0 # make_zeros (n - 1)"

definition make_empty_bytes :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat list" where
  "make_empty_bytes dev numberb = n64bytes numberb @ make_zeros (bs dev - 8)"

definition make_empty_block :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat list" where
  "make_empty_block dev numberb = make_empty_bytes dev (numberb * bs dev)"

definition blocks_for_bytes :: "'a device_scheme  \<Rightarrow> nat \<Rightarrow> nat" where
  "blocks_for_bytes dev n = (n + bs dev - 1) div bs dev"

definition zero :: "'a device_scheme \<Rightarrow> nat list" where
 "zero dev = make_zeros (bs dev)"

function write_all :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> unit" where
  "write_all dev n = (
      if n \<ge> nb dev then ()
      else let _ = w dev n (make_zeros (bs dev)) in write_all dev (n + 1))"
   apply auto
   done

definition format :: "'a device_scheme \<Rightarrow> unit" where
  "format dev =       
      (if bs dev \<le> 9 then ()
       else
       let _ = write_all dev 1 in
       w dev 0 (make_empty_block dev (nb dev)))"


function helper :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)" where
"helper dev bn hsize = 
                 (if bn > (nb dev) then (0, 0)
                 else
                 let block = r dev bn in
                 let blocks = blocks_for_bytes dev hsize in
                 let fsize = bytes64 block in
                 let nb = blocks_for_bytes dev fsize in
                 let name = restn block 8 in      
                 (if nb >= blocks \<and> getn name 1 = [0] then    
                    (if nb > blocks then           
                       let num_empty = nb - blocks in
                       let new_empty = make_empty_block dev num_empty in
                       let new_bn = bn + blocks in
                       let _ =  w dev new_bn new_empty in (bn, nb)
                    else (0,0))
                 else 
                  helper dev (bn + nb) hsize))"
   apply auto
   done

(* Find an unused block with at least `size` bytes *)
fun find_empty :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)" where
  "find_empty dev hsize = helper dev 0 hsize"

fun separate_name :: "nat list \<Rightarrow> nat list \<times> nat list" where
  "separate_name [] = ([], [])"
| "separate_name (0 # rest) = ([0], rest)"
| "separate_name (c # rest) = 
    (let (name_end, list) = separate_name rest 
     in (c # name_end, list))"

definition internal_get_header :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat list \<times> nat list \<times> nat list) " where
  "internal_get_header dev bn = 
                     (let block = r dev bn in
                      let fsize = bytes64 block in
                      let nb = blocks_for_bytes dev fsize in
                      let fname_plus = restn block 8 in
                      let (fname, initial_data) = separate_name fname_plus in
                       (fsize, nb, fname, initial_data, block))"


definition char_to_nat :: "char \<Rightarrow> nat" where
  "char_to_nat c = of_char c"

definition name_to_list :: "String.literal \<Rightarrow> nat list" where
  "name_to_list lname = (map char_to_nat (String.explode lname)) @ [0]"

(*value"name_to_list STR ''shu4''"*)

fun clear_file :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> unit" where
  "clear_file dev bn numberb zero_block = (if numberb \<le> 0 then () 
                                  else
                                      let _ = w dev numberb zero_block in
                                      clear_file dev (bn + 1) (numberb - 1) zero_block)"

fun remove_file :: "String.literal \<Rightarrow> (String.literal \<times> nat list) list \<Rightarrow> (String.literal \<times> nat list) list" where
  "remove_file _ [] = []" |
  "remove_file tname ((fname, fcontent) # rest) =
     (if fname = tname then rest else (fname, fcontent) # remove_file tname rest)"

(*value "remove_file STR ''file1'' [( STR ''file1'', [1, 2, 3] ), ( STR ''file2'', [4, 5, 6] )]"*)

fun get_next :: "nat \<Rightarrow>'a device_scheme \<Rightarrow> nat" where
  "get_next bn dev = (if bn \<ge> nb dev then 0
                      else let (_, numberb, fname, _, _) = internal_get_header dev (nb dev) in
                      (if length fname = 1 then let _ =  w dev bn (make_zeros (bs dev)) in numberb
                       else 0))"

fun internal_delete_file :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>nat \<Rightarrow> unit" where
"internal_delete_file dev bn numberb prev_bn prev_nb = 
            (let next_nb = get_next (bn + numberb) dev in
            let size_from_bn =  (numberb + next_nb) * (bs dev) in
            let max_bytes =  size_from_bn + prev_nb *  (bs dev) in
            let _ = clear_file dev bn numberb (make_zeros (bs dev)) in
            (if prev_bn = 0 then
            w dev bn (make_empty_bytes dev size_from_bn)
            else 
            w dev prev_bn (make_empty_bytes dev max_bytes)))"

function read_all :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"read_all dev  block_num remaining_size = 
                                    (let block = r dev block_num in
                                    if  remaining_size > (bs dev) then
                                    block @ read_all dev (block_num + 1) (remaining_size - (bs dev))
                                    else getn block remaining_size)"
   apply auto
  done

fun compare_byte_lists :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "compare_byte_lists fname1 fname2 = (fname1 = fname2)"

(*value"compare_byte_lists (name_to_list STR ''shu4'') [115, 104, 117, 53, 0]"*)

function find_file :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat list option" where
  "find_file dev bn prev_bn prev_numberb lname do_delete =
    (if bn \<ge> nb dev then None
     else
      let (fsize, numberb, fname, initial_data, block) = internal_get_header dev bn in
      let hsize = 8 + length fname in
      let dsize = fsize - hsize in
      let next_bn = bn + 1 in
      if compare_byte_lists lname fname then
        let result = 
          if fsize \<le> bs dev then 
            getn initial_data dsize
          else 
            initial_data @ read_all dev next_bn (fsize - bs dev) in
            let _ = 
              (if do_delete then internal_delete_file dev bn numberb prev_bn prev_numberb 
               else ()) 
            in Some result
      else
        if length fname = 1 then
          find_file dev (bn + numberb) bn numberb lname do_delete
        else
          find_file dev (bn + numberb) 0 0 lname do_delete)"
   apply auto
  done

definition internal_read_or_delete :: "bool \<Rightarrow> 'a device_scheme \<Rightarrow> String.literal \<Rightarrow> nat list option" where
  " internal_read_or_delete do_delete dev fname = 
        (let lname = name_to_list 0 in
        find_file dev 0 0 0 lname do_delete)"

function write_data :: "'a device_scheme \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> unit" where
  "write_data dev bn data dlen =
    (if dlen \<le> bs dev then
       w dev bn (data @ make_zeros (bs dev - dlen))
     else
       let first = getn data (bs dev) in
       let rest = restn data (bs dev) in
       let _ = w dev bn first in
        write_data dev (bn + 1) rest (dlen - bs dev))"
   apply auto
  done

definition read_file :: "'a device_scheme \<Rightarrow> String.literal \<Rightarrow> nat list option" where
  "read_file dev fname = internal_read_or_delete False dev fname"

definition delete_file :: "'a device_scheme \<Rightarrow> String.literal \<Rightarrow> nat list option" where
  "delete_file dev fname = internal_read_or_delete True dev fname"

definition new_file :: "'a device_scheme \<Rightarrow> String.literal \<Rightarrow> nat list \<Rightarrow> unit" where
"new_file dev fname data = 
  (if read_file dev fname = None \<and> (length (String.explode fname) + 9) < bs dev then
    let lname = name_to_list 0 in
    let size = 8 + length lname + length data in
    let all_data = n64bytes size @ lname @ data in
    let (bn, numberb) = find_empty dev size in
    if bn < 0 then ()
    else write_data dev bn all_data size
  else if (length (String.explode fname))+ 9 \<ge> bs dev then ()
  else ())"

end