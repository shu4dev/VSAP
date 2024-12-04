(* simple as possible file system: (inefficient, only for small devices)
 * list of block groups (BG), each of which is a file or empty spaces.
 * a BG begins with a 64-bit/8-byte size in bytes, then the name, then the data
 * the size includes the initial 8 bytes and the null-terminated name
 * for an empty space, the name is empty, meaning only the null byte. *)

 type device = { 
  name: string; 
  bs: int64; 
  nb: int64;
  r: int64 -> int list; 
  w: int64 -> int list -> unit }

(* 1. assert: every write operation in this program writes device.bs bytes,
*            every read operation after calling format reads device.bs bytes *)
(* 2. assert: the name of every file fits in device.bs - 9 (see new_file) *)
(* 3. assert: unless there are errors, every file written is accessible
until a matching delete_file (or forever). *)

let check_invariant1 bs lst = assert (Int64.of_int (List.length lst) = bs)
let check_invariant2 bs name =
assert (List.length name <= (Int64.to_int bs) - 9)

(* generic functions for groups of bytes *)
let rec getn lst n =    (* get n bytes from the list *)
if n <= 0 then []
else match lst with
| [] -> failwith "insufficient bytes"
| first :: rest -> first :: (getn rest (n - 1))

let rec restn lst n =   (* remove first n bytes from the list *)
if n <= 0 then lst
else match lst with
| [] -> failwith "unable to skip over n bytes"
| _ :: rest -> restn rest (n - 1)

(* convert a 64-bit number to a list of bytes and get from a list of bytes *)
let n64bytes n =
let rec make_rev_bytes x index =
if index <= 0 then []
else (Int64.to_int (Int64.rem x 256L)) ::
make_rev_bytes (Int64.div x 256L) (index - 1) in
List.rev (make_rev_bytes n 8)

let bytes64 lst =
let first8 = getn lst 8 in
let rec compute lst =    (* lst has the lsb first *)
match lst with
| [] -> 0L
| first :: rest ->
(assert (first >= 0); assert (first < 256);
(Int64.add (Int64.of_int first)
          (Int64.mul (compute rest) 256L))) in
compute (List.rev first8)

(* 4. assert bytes64 (n64bytes n) = n for any n < 2^63 *)
(* 5. assert n64bytes (bytes64 l) = l for any list of int<256 of length = 8 *)
let check_invariant45 () =
let n = Random.int64 2147483646L in
let rec make_list = function
| 0 -> []
| l -> (Random.int 256) :: (make_list (l - 1)) in
let make_first_less_than_128 = function
| [] -> failwith "illegal list does not have first"
| first :: rest ->
  (if first >= 128 then first - 128 else first) :: rest in
let rec list_to_string = function
| [] -> ""
| first :: rest ->
 (string_of_int first) ^ "." ^ (list_to_string rest) in
let random_list = make_first_less_than_128 (make_list 8) in
(print_string "random int is " ; print_endline (Int64.to_string n);
print_string "random list is " ;
print_endline (list_to_string random_list);
print_string "random list is now " ;
print_endline (list_to_string (n64bytes (bytes64 random_list)));
assert (bytes64 (n64bytes n) = n);
assert (n64bytes (bytes64 random_list) = random_list))

let _ = Random.self_init()
let _ = check_invariant45();;

(* make a list of n zeros *)
let rec make_zeros n =
if n = 0L then []
else 0 :: (make_zeros (Int64.sub n 1L))

(* create a block marking an empty set of nb blocks or bytes *)
let rec make_empty_bytes device nb = n64bytes nb @
                      make_zeros (Int64.sub device.bs 8L)
                      
let rec make_empty_block device nb =
make_empty_bytes device (Int64.mul nb device.bs)

let blocks_for_bytes device n =
Int64.div (Int64.add n (Int64.sub device.bs 1L)) device.bs

(* clear the device and create an empty set of all blocks *)
let format device =
let _ = assert (device.bs > 9L) in
let zeros = make_zeros device.bs in
let rec write_all n =
if n >= device.nb then ()
else (device.w n zeros; write_all (Int64.add n 1L)) in
(write_all 1L;
device.w 0L (make_empty_block device device.nb))

(* find an unused block with at least size bytes *)
let find_empty device size =  (* size includes 8+namelen+1 bytes of header *)
let blocks = blocks_for_bytes device size in
let rec helper bn =
if bn >= device.nb then (-1L, 0L)       (* not found *)
else
 (let block = device.r bn in
  let fsize = bytes64 block in       (* size in bytes *)
  let nb = blocks_for_bytes device fsize in (* size in blocks *)
  let name = restn block 8 in
  if nb >= blocks && getn name 1 = [0] then  (* empty block *)
    (if nb > blocks then             (* some free space *)
       let num_empty = Int64.sub nb blocks in
       let new_empty = make_empty_block device num_empty
       and new_bn = Int64.add bn blocks in
       device.w new_bn new_empty
     else ();
     (bn, nb))
  else                            (* go to next block *)
    helper (Int64.add bn nb)) in
helper 0L

(* used in the invariants checking *)
let read_errors = ref 0
let write_errors = ref 0
let files_created = ref ([]: (string * int list) list)
let remove_file_from_created name =
let rec remove_file = function
| [] -> []  (* fail silently if the file doesn't exist *)
| (fname, fcontent) :: rest ->
 if fname = name then rest
 else (fname, fcontent) :: (remove_file rest) in
files_created := remove_file (! files_created)

let rec compare_byte_lists n c1 c2 = match (c1, c2, n) with
| ([], [], _) -> true
| (_ :: _, [], None) -> false
| (_ :: _, [], Some _) -> print_endline "c1 is longer"; false
| ([], _ :: _, None) -> false
| ([], _ :: _, Some _) -> print_endline "c2 is longer"; false
| (h1 :: r1, h2 :: r2, None) ->
h1 = h2 && compare_byte_lists None r1 r2
| (h1 :: r1, h2 :: r2, Some elt) ->
(if h1 != h2 then
 (print_int elt; print_string ": ";
  print_int h1; print_string " != ";
  print_int h2; print_endline ""; false)
else compare_byte_lists (Some (elt + 1)) r1 r2)

let internal_get_header device bn =
let block = device.r bn in
let fsize = bytes64 block in       (* size in bytes *)
let nb = blocks_for_bytes device fsize in (* size in blocks *)
let fname_plus = restn block 8 in
let rec separate_name = function
| [] -> ([], [])
| 0 :: rest -> ([0], rest)
| c :: rest ->
 let (name_end, list) = separate_name rest in
 (c :: name_end, list) in
let (fname, initial_data) = separate_name fname_plus in
check_invariant2 device.bs fname;
(fsize, nb, fname, initial_data, block)

let blocks_read = ref []

(* read or delete are almost the same, so do both in the same function *)
let internal_read_or_delete do_delete device name =

let rec name_to_list pos =
if pos = String.length name then [0]
else (Char.code (String.get name pos)) ::
    name_to_list (pos + 1) in

let lname = name_to_list 0 in

let rec clear_file bn nb zero_block =
if nb <= 0L then ()
else (device.w bn zero_block;
     clear_file (Int64.add bn 1L) (Int64.sub nb 1L) zero_block) in

let rec delete_file bn nb prev_bn prev_nb =
let _ = remove_file_from_created name in
let get_next bn =
    if bn >= device.nb then 0L
    else (let (_, nb, fname, _, _) =
               internal_get_header device bn in
          if List.length fname = 1 then
            (device.w bn (make_zeros device.bs);
             nb)
          else 0L) in
let next_nb = get_next (Int64.add bn nb) in
let size_from_bn = Int64.mul (Int64.add nb next_nb) device.bs in
let max_bytes = Int64.add size_from_bn
                         (Int64.mul prev_nb device.bs) in
(clear_file bn nb (make_zeros device.bs);
if prev_bn = -1L then
  device.w bn (make_empty_bytes device size_from_bn)
else
  device.w prev_bn (make_empty_bytes device max_bytes)) in

let rec read_all block_num remaining_size =
let block = device.r block_num in
if remaining_size > device.bs then
  block @ (read_all (Int64.add block_num 1L)
                    (Int64.sub remaining_size device.bs))
else getn block (Int64.to_int remaining_size) in


let rec find_file bn prev_bn prev_nb =
if bn >= device.nb then None          (* not found *)
else
 (let (fsize, nb, fname, initial_data, block) =
        internal_get_header device bn in
  let hsize = Int64.of_int (8 + List.length fname) in
  let dsize = Int64.sub fsize hsize in
  let next_bn = Int64.add bn 1L in
  if compare_byte_lists None lname fname then       (* found *)
    (let result =
       if fsize <= device.bs then getn initial_data
                                       (Int64.to_int dsize)
       else initial_data @
            (read_all next_bn (Int64.sub fsize device.bs)) in
     (if do_delete then delete_file bn nb prev_bn prev_nb
      else ();
      Some result))
  else                               (* not found *)
    (if List.length fname = 1 then   (* empty, possible merge *)
       find_file (Int64.add bn nb) bn nb
     else find_file (Int64.add bn nb) (-1L) (-1L))) in
     
let result = find_file 0L (-1L) (-1L) in

result

let check_invariant3 dev =
if ! read_errors = 0 && ! write_errors = 0 then
(let rec verify_files = function
| [] -> true
| (name, content) :: rest ->
 (match internal_read_or_delete false dev name with
  | None -> print_endline (name ^ " not found"); false
  | Some c ->
      if compare_byte_lists (Some 0) c content
      then verify_files rest
      else (print_endline (name ^ " not same");
            print_int (List.length c);
            print_string " =? ";
            print_int (List.length content);
            print_endline "";
            false)) in
assert (verify_files (! files_created)))
else ()

let read_file device name =
check_invariant3 device;
internal_read_or_delete false device name

let delete_file device name =
check_invariant3 device;
internal_read_or_delete true device name

(* create a new file with the given data *)
let new_file device name data =

let _ = check_invariant3 device in
if read_file device name = None &&
(Int64.of_int (String.length name + 9)) < device.bs then
(let rec name_to_list pos =
   if pos = String.length name then [0]
   else (Char.code (String.get name pos)) ::
        name_to_list (pos + 1) in

let lname = name_to_list 0 in

let rec write_data bn data dlen =
   if dlen <= device.bs then
     device.w bn (data @ (make_zeros (Int64.sub device.bs dlen)))
   else
     let first = getn data (Int64.to_int device.bs)
     and rest = restn data (Int64.to_int device.bs) in
     (device.w bn first;
      write_data (Int64.add bn 1L) rest
                 (Int64.sub dlen device.bs)) in

let size = Int64.of_int (8 + (List.length lname) + (List.length data)) in
let all_data = (n64bytes size) @ lname @ data in
let (bn, nb) = find_empty device size in
if bn < 0L then failwith "unable to create file"
else files_created := (name, data) :: (! files_created);
write_data bn all_data size)

else if Int64.of_int (String.length name + 9) >= device.bs then
failwith "new_file name too long"

else
failwith ("file " ^ name ^ " already exists")

let list_files device =
let list_to_name name =
let int_to_string i = String.make 1 (Char.chr i) in
let substrings = List.map int_to_string name in
String.concat "" substrings in
let rec helper bn =
if bn >= device.nb then []          (* no more files *)
else
let (fsize, nb, fname, initial_data, block) =
   internal_get_header device bn in
let name = list_to_name (getn fname (List.length fname - 1)) in
let hsize = Int64.of_int (8 + List.length fname) in
let dsize = Int64.sub fsize hsize in
let others = helper (Int64.add bn nb) in
if List.length fname > 1 then (name, bn, dsize) :: others
                      else others in
check_invariant3 device;
helper 0L

(* test stuff *)
let blocks = Array.make 500 []
let read_block bs n =
let data = Array.get blocks (Int64.to_int n) in
check_invariant1 bs data;
data

(* let write_block n b = Array.set blocks n b *)
let write_block bs n b =
check_invariant1 bs b;
Array.set blocks (Int64.to_int n) b
let dev = let bs = 512L in
{ name = "test"; bs = bs; nb = 100L; r = read_block bs; w = write_block bs }
let rec make_data = function
| 0 -> []
| n -> (n mod 256) :: make_data (n - 1)
let data = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]
(* two blocks' worth of data *)
let ld = data @ data @ data @ data @ data @ data @ data @ data @ data @ data @
data @ data @ data @ data @ data @ data @ data @ data @ data @ data @
data @ data @ data @ data @ data @ data @ data @ data @ data @ data @
data @ data @ data @ data @ data @ data @ data @ data @ data @ data @
data @ data @ data @ data @ data @ data @ data @ data @ data @ data @
data @ data @ data @ data @ data @ data @ data @ data @ data @ data @
data @ data @ data @ data @ data @ data @ data @ data @ data @ data

let rec make_files device = function
| [] -> ()
| (fname, fsize) :: rest ->
(print_endline ("making file " ^ fname);
new_file device fname (make_data fsize);
make_files device rest)
let sample_files1 = [("a", 10); ("b", 600); ("c", 512); ("d", 500); ("e", 501);
      ("f", 502); ("g", 503); ("h", 504); ("i", 505);
      ("j", 10000); ("k", 1); ("l", 0)]

(* print the non-zero part of non-zero blocks *)
let print_blocks device max =
let blen = Int64.of_int (Array.length blocks) in
let dlen = if device.nb < blen then device.nb else blen in
let actual_max = if max <= 0L || max > dlen then dlen else max in
let rec is_zeros = function
| [] -> true
| 0 :: rest -> is_zeros rest
| _ -> false in
let rec print_block lst min =
if min <= 0L && is_zeros lst then ()
else match lst with
    | [] -> if min <= 0L then failwith "no bytes in print_block"
            else print_block (make_zeros min) min
    | first :: rest ->
       print_int first;
       print_string " ";
       print_block rest (Int64.sub min 1L) in
let rec print_all n =
if n < actual_max then
 (let a = read_block device.bs n in
  if is_zeros a then ()
  else
    (print_int (Int64.to_int n);
     print_string ": ";
     print_block a 8L;
     print_endline "");
  print_all (Int64.add n 1L))
else () in
print_all 0L

let p () = print_blocks dev 0L
