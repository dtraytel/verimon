(* The OCaml functions that the code of thys/VeriMon_CLI is printed with (theory CLI_Code), besides
   Zarith's and the standard library's. *)

let digits = Bytes.create 20

(* The decimal representation of an integer, as [Z.to_string], without the formatting of
   [Z.to_string] and [string_of_int] for the integers that fit into an OCaml integer. *)
let dec_of_z i =
  if not (Z.fits_int i) then Z.to_string i
  else begin
    let n = Z.to_int i in
    if n = 0 then "0"
    else if n = min_int then string_of_int n
    else begin
      let neg = n < 0 in
      let rec go n k =
        if n = 0 then k
        else begin Bytes.unsafe_set digits k (Char.unsafe_chr (48 + n mod 10)); go (n / 10) (k - 1) end in
      let k = go (abs n) 19 in
      let k = if neg then (Bytes.unsafe_set digits k '-'; k - 1) else k in
      Bytes.sub_string digits (k + 1) (19 - k)
    end
  end

(* [Buffer.add_string b (dec_of_z i)], without building the string. *)
let add_dec_of_z b i =
  if not (Z.fits_int i) then Buffer.add_string b (Z.to_string i)
  else begin
    let n = Z.to_int i in
    if n = 0 then Buffer.add_char b '0'
    else if n = min_int then Buffer.add_string b (string_of_int n)
    else begin
      if n < 0 then Buffer.add_char b '-';
      let rec go n k =
        if n = 0 then k
        else begin Bytes.unsafe_set digits k (Char.unsafe_chr (48 + n mod 10)); go (n / 10) (k - 1) end in
      let k = go (abs n) 19 in
      Buffer.add_subbytes b digits (k + 1) (19 - k)
    end
  end
