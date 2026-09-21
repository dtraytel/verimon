module Config : sig
  val generic_join : bool ref
  val imperative_join : bool ref
  val bulk_min : int ref
end = struct
  let generic_join = ref false
  let imperative_join = ref false
  let bulk_min = ref 64
end

module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val shiftl : int32 -> Z.t -> int32
  val shiftr : int32 -> Z.t -> int32
  val shiftr_signed : int32 -> Z.t -> int32
  val test_bit : int32 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let shiftl x n = Int32.shift_left x (Z.to_int n);;

let shiftr x n = Int32.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int32.shift_right x (Z.to_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Z.to_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)

module ConfigImp : sig
  val heap_join_min : int ref
  val dense_heap_join : bool ref
end = struct
  let heap_join_min = ref 0
  let dense_heap_join = ref false
end

module FloatUtil : sig
  val iszero : float -> bool
  val isinfinite : float -> bool
  val isnan : float -> bool
  val copysign : float -> float -> float
  val compare : float -> float -> Z.t
end = struct
  let iszero x = (Stdlib.classify_float x = Stdlib.FP_zero);;
  let isinfinite x = (Stdlib.classify_float x = Stdlib.FP_infinite);;
  let isnan x = (Stdlib.classify_float x = Stdlib.FP_nan);;
  let copysign x y = if isnan y then Stdlib.nan else Stdlib.copysign x y;;
  let compare x y = Z.of_int (Stdlib.compare x y);;
end;;

module Monitor : sig
  type nat
  val integer_of_nat : nat -> Z.t
  type ('a, 'b) phantom
  type mapping_impla
  type ('b, 'a) mapping_rbt
  type 'a set_dlist
  type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
    RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
    Complement of 'a set
  val nat_of_integer : Z.t -> nat
  type event_data = EInt of Z.t | EFloat of float | EString of string
  type trm = Var of nat | Const of event_data | Plus of trm * trm |
    Minus of trm * trm | UMinus of trm | Mult of trm * trm | Div of trm * trm |
    Mod of trm * trm | F2i of trm | I2f of trm
  type mregex
  type enat = Enat of nat | Infinity_enat
  type rec_safety
  type ('a, 'b) mapping
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  type 'a queue
  type uduaux_x
  type aggaux
  type agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
  type ty = TInt | TFloat | TString
  type udsaux_x
  type i
  type 'a args_ext
  type 'a mbuf_t
  type mconstraint
  type djoin_plan
  type mtrm
  type udformula
  type int = Int_of_integer of Z.t
  type 'a regex = Skip of nat | Test of 'a | Plusa of 'a regex * 'a regex |
    Times of 'a regex * 'a regex | Star of 'a regex
  type safety
  type tysym = TAny of nat | TNum of nat | TCst of ty
  type modality
  type 'a formula = Pred of string * trm list |
    Let of string * 'a formula * 'a formula |
    Frz of string * 'a formula * 'a formula |
    LetPast of string * 'a formula * 'a formula | Eq of trm * trm |
    Less of trm * trm | LessEq of trm * trm | Neg of 'a formula |
    Or of 'a formula * 'a formula | And of 'a formula * 'a formula |
    Ands of 'a formula list | Exists of 'a * 'a formula |
    Agg of nat * (agg_type * 'a) * 'a list * trm * 'a formula |
    Prev of i * 'a formula | Next of i * 'a formula |
    Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula
    | Trigger of 'a formula * i * 'a formula |
    Release of 'a formula * i * 'a formula | MatchF of i * 'a formula regex |
    MatchP of i * 'a formula regex | TP of trm | TS of trm
  type ('a, 'b, 'c) meformula
  type msaux_d
  type muaux_d
  type 'a wf_table
  type dformula
  type 'a boxed
  type ('a, 'b, 'c, 'd) mstate_ext
  type muaux_dq
  type 'a udmstate_ext
  val wild : 'a regex
  val integer_of_int : int -> Z.t
  val mstep_d :
    ((string * nat), ((event_data list) set list)) mapping * nat ->
      nat * (nat * (dformula * (nat * nat queue))) ->
        (unit ->
          ((nat * (nat * (event_data list) set)) list *
            (nat * (nat * (dformula * (nat * nat queue))))))
  val interval : nat -> enat -> i
  val type_check :
    (string * nat -> (tysym list) option) ->
      tysym formula -> (string, ty formula) sum
  val dfail_nodes : dformula -> nat
  val minit_safe_d :
    ty formula -> (unit -> (nat * (nat * (dformula * (nat * nat queue)))))
  val mmonitorable_exec : 'a formula -> bool
  val convert_multiway : 'a formula -> 'a formula
  val uempty_db : ((string * nat), ((event_data list) set list)) mapping
  val urbt_fold :
    (event_data list -> 'a -> 'a) ->
      ((event_data list), unit) mapping_rbt -> 'a -> 'a
  val udmstate_m : 'a udmstate_ext -> udformula
  val udmstep :
    ((string * nat), ((event_data list) set list)) mapping * nat ->
      unit udmstate_ext ->
        (nat * (nat * (event_data list) set)) list * unit udmstate_ext
  val utable_of_list : (event_data list) list -> (event_data list) set
  val udminit_safe : ty formula -> unit udmstate_ext
  val uvdfail_nodes : udformula -> nat
  val uinsert_table_into_db :
    string * nat ->
      (event_data list) set ->
        ((string * nat), ((event_data list) set list)) mapping ->
          ((string * nat), ((event_data list) set list)) mapping
end = struct

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

type typerepa = Typerep of string * typerepa list;;

type 'a itself = Type;;

let rec typerep_nata t = Typerep ("Nat.nat", []);;

type 'a typerep = {typerep : 'a itself -> typerepa};;
let typerep _A = _A.typerep;;

type 'a countable = unit;;

type 'a heap = {countable_heap : 'a countable; typerep_heap : 'a typerep};;

let countable_nat = (() : nat countable);;

let typerep_nat = ({typerep = typerep_nata} : nat typerep);;

let heap_nat =
  ({countable_heap = countable_nat; typerep_heap = typerep_nat} : nat heap);;

let rec times_nata m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_nat = ({times = times_nata} : nat times);;

let dvd_nat = ({times_dvd = times_nat} : nat dvd);;

type num = One | Bit0 of num | Bit1 of num;;

let one_nata : nat = Nat (Z.of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec plus_nata m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_nat = ({plus = plus_nata} : nat plus);;

let zero_nata : nat = Nat Z.zero;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_nat = ({zero = zero_nata} : nat zero);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let semigroup_add_nat = ({plus_semigroup_add = plus_nat} : nat semigroup_add);;

let numeral_nat =
  ({one_numeral = one_nat; semigroup_add_numeral = semigroup_add_nat} :
    nat numeral);;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

let rec ed_max_integer a b = (if Z.leq a b then b else a);;

let rec minus_nata
  m n = Nat (ed_max_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

let minus_nat = ({minus = minus_nata} : nat minus);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec inf_nata x = min ord_nat x;;

type 'a inf = {inf : 'a -> 'a -> 'a};;
let inf _A = _A.inf;;

let inf_nat = ({inf = inf_nata} : nat inf);;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec sup_nata x = max ord_nat x;;

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_nat = ({sup = sup_nata} : nat sup);;

let rec apsnd f (x, y) = (x, f y);;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec fst p = (let (a, _) = p in a);;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nata
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

let divide_nat = ({divide = divide_nata} : nat divide);;

let rec snd p = (let (_, b) = p in b);;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_nata
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

type 'a modulo =
  {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a};;
let modulo _A = _A.modulo;;

let modulo_nat =
  ({divide_modulo = divide_nat; dvd_modulo = dvd_nat; modulo = modulo_nata} :
    nat modulo);;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

type 'a interval =
  {linorder_interval : 'a linorder;
    comm_semiring_1_cancel_interval : 'a comm_semiring_1_cancel};;

let cancel_semigroup_add_nat =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
    nat cancel_semigroup_add);;

let ab_semigroup_add_nat =
  ({semigroup_add_ab_semigroup_add = semigroup_add_nat} :
    nat ab_semigroup_add);;

let cancel_ab_semigroup_add_nat =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat;
     minus_cancel_ab_semigroup_add = minus_nat}
    : nat cancel_ab_semigroup_add);;

let monoid_add_nat =
  ({semigroup_add_monoid_add = semigroup_add_nat; zero_monoid_add = zero_nat} :
    nat monoid_add);;

let comm_monoid_add_nat =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat;
     monoid_add_comm_monoid_add = monoid_add_nat}
    : nat comm_monoid_add);;

let cancel_comm_monoid_add_nat =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_nat;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
    : nat cancel_comm_monoid_add);;

let mult_zero_nat =
  ({times_mult_zero = times_nat; zero_mult_zero = zero_nat} : nat mult_zero);;

let semigroup_mult_nat =
  ({times_semigroup_mult = times_nat} : nat semigroup_mult);;

let semiring_nat =
  ({ab_semigroup_add_semiring = ab_semigroup_add_nat;
     semigroup_mult_semiring = semigroup_mult_nat}
    : nat semiring);;

let semiring_0_nat =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_nat;
     mult_zero_semiring_0 = mult_zero_nat; semiring_semiring_0 = semiring_nat}
    : nat semiring_0);;

let semiring_0_cancel_nat =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat;
     semiring_0_semiring_0_cancel = semiring_0_nat}
    : nat semiring_0_cancel);;

let ab_semigroup_mult_nat =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
    nat ab_semigroup_mult);;

let comm_semiring_nat =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat;
     semiring_comm_semiring = semiring_nat}
    : nat comm_semiring);;

let comm_semiring_0_nat =
  ({comm_semiring_comm_semiring_0 = comm_semiring_nat;
     semiring_0_comm_semiring_0 = semiring_0_nat}
    : nat comm_semiring_0);;

let comm_semiring_0_cancel_nat =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
    : nat comm_semiring_0_cancel);;

let monoid_mult_nat =
  ({semigroup_mult_monoid_mult = semigroup_mult_nat;
     power_monoid_mult = power_nat}
    : nat monoid_mult);;

let semiring_numeral_nat =
  ({monoid_mult_semiring_numeral = monoid_mult_nat;
     numeral_semiring_numeral = numeral_nat;
     semiring_semiring_numeral = semiring_nat}
    : nat semiring_numeral);;

let zero_neq_one_nat =
  ({one_zero_neq_one = one_nat; zero_zero_neq_one = zero_nat} :
    nat zero_neq_one);;

let semiring_1_nat =
  ({semiring_numeral_semiring_1 = semiring_numeral_nat;
     semiring_0_semiring_1 = semiring_0_nat;
     zero_neq_one_semiring_1 = zero_neq_one_nat}
    : nat semiring_1);;

let semiring_1_cancel_nat =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat;
     semiring_1_semiring_1_cancel = semiring_1_nat}
    : nat semiring_1_cancel);;

let comm_monoid_mult_nat =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat;
     monoid_mult_comm_monoid_mult = monoid_mult_nat;
     dvd_comm_monoid_mult = dvd_nat}
    : nat comm_monoid_mult);;

let comm_semiring_1_nat =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat;
     semiring_1_comm_semiring_1 = semiring_1_nat}
    : nat comm_semiring_1);;

let comm_semiring_1_cancel_nat =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
    : nat comm_semiring_1_cancel);;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let interval_nat =
  ({linorder_interval = linorder_nat;
     comm_semiring_1_cancel_interval = comm_semiring_1_cancel_nat}
    : nat interval);;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1;
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel;
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};;

let semiring_no_zero_divisors_nat =
  ({semiring_0_semiring_no_zero_divisors = semiring_0_nat} :
    nat semiring_no_zero_divisors);;

let semiring_1_no_zero_divisors_nat =
  ({semiring_1_semiring_1_no_zero_divisors = semiring_1_nat;
     semiring_no_zero_divisors_semiring_1_no_zero_divisors =
       semiring_no_zero_divisors_nat}
    : nat semiring_1_no_zero_divisors);;

let semidom_nat =
  ({comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_nat;
     semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_nat}
    : nat semidom);;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

type 'a semilattice_inf =
  {inf_semilattice_inf : 'a inf; order_semilattice_inf : 'a order};;

type 'a lattice =
  {semilattice_inf_lattice : 'a semilattice_inf;
    semilattice_sup_lattice : 'a semilattice_sup};;

let semilattice_sup_nat =
  ({sup_semilattice_sup = sup_nat; order_semilattice_sup = order_nat} :
    nat semilattice_sup);;

let semilattice_inf_nat =
  ({inf_semilattice_inf = inf_nat; order_semilattice_inf = order_nat} :
    nat semilattice_inf);;

let lattice_nat =
  ({semilattice_inf_lattice = semilattice_inf_nat;
     semilattice_sup_lattice = semilattice_sup_nat}
    : nat lattice);;

let ceq_nata : (nat -> nat -> bool) option = Some equal_nata;;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};;
let ceq _A = _A.ceq;;

let ceq_nat = ({ceq = ceq_nata} : nat ceq);;

type ('a, 'b) phantom = Phantom of 'b;;

type set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada;;

let set_impl_nata : (nat, set_impla) phantom = Phantom Set_RBT;;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};;
let set_impl _A = _A.set_impl;;

let set_impl_nat = ({set_impl = set_impl_nata} : nat set_impl);;

type 'a divide_trivial =
  {one_divide_trivial : 'a one; zero_divide_trivial : 'a zero;
    divide_divide_trivial : 'a divide};;

let divide_trivial_nat =
  ({one_divide_trivial = one_nat; zero_divide_trivial = zero_nat;
     divide_divide_trivial = divide_nat}
    : nat divide_trivial);;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};;

type 'a semidom_divide =
  {divide_trivial_semidom_divide : 'a divide_trivial;
    semidom_semidom_divide : 'a semidom;
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};;

let semiring_no_zero_divisors_cancel_nat =
  ({semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
      semiring_no_zero_divisors_nat}
    : nat semiring_no_zero_divisors_cancel);;

let semidom_divide_nat =
  ({divide_trivial_semidom_divide = divide_trivial_nat;
     semidom_semidom_divide = semidom_nat;
     semiring_no_zero_divisors_cancel_semidom_divide =
       semiring_no_zero_divisors_cancel_nat}
    : nat semidom_divide);;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
    modulo_semiring_modulo : 'a modulo};;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial;
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
    semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial};;

let semiring_modulo_nat =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_nat;
     modulo_semiring_modulo = modulo_nat}
    : nat semiring_modulo);;

let semiring_modulo_trivial_nat =
  ({divide_trivial_semiring_modulo_trivial = divide_trivial_nat;
     semiring_modulo_semiring_modulo_trivial = semiring_modulo_nat}
    : nat semiring_modulo_trivial);;

let algebraic_semidom_nat =
  ({semidom_divide_algebraic_semidom = semidom_divide_nat} :
    nat algebraic_semidom);;

let semidom_modulo_nat =
  ({algebraic_semidom_semidom_modulo = algebraic_semidom_nat;
     semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_nat}
    : nat semidom_modulo);;

let finite_UNIV_nata : (nat, bool) phantom = Phantom false;;

let card_UNIV_nata : (nat, nat) phantom = Phantom zero_nata;;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};;
let finite_UNIV _A = _A.finite_UNIV;;

type 'a card_UNIV =
  {finite_UNIV_card_UNIV : 'a finite_UNIV; card_UNIV : ('a, nat) phantom};;
let card_UNIV _A = _A.card_UNIV;;

let finite_UNIV_nat = ({finite_UNIV = finite_UNIV_nata} : nat finite_UNIV);;

let card_UNIV_nat =
  ({finite_UNIV_card_UNIV = finite_UNIV_nat; card_UNIV = card_UNIV_nata} :
    nat card_UNIV);;

let cEnum_nat :
  (nat list * (((nat -> bool) -> bool) * ((nat -> bool) -> bool))) option
  = None;;

type 'a cenum =
  {cEnum :
     ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option};;
let cEnum _A = _A.cEnum;;

let cenum_nat = ({cEnum = cEnum_nat} : nat cenum);;

type ordera = Eqa | Lt | Gt;;

let rec compare_nat
  x y = (if less_nat x y then Lt else (if equal_nata x y then Eqa else Gt));;

let ccompare_nata : (nat -> nat -> ordera) option = Some compare_nat;;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};;
let ccompare _A = _A.ccompare;;

let ccompare_nat = ({ccompare = ccompare_nata} : nat ccompare);;

type mapping_impla = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT |
  Mapping_Mapping;;

let mapping_impl_nata : (nat, mapping_impla) phantom = Phantom Mapping_RBT;;

type 'a mapping_impl = {mapping_impl : ('a, mapping_impla) phantom};;
let mapping_impl _A = _A.mapping_impl;;

let mapping_impl_nat = ({mapping_impl = mapping_impl_nata} : nat mapping_impl);;

let rec proper_interval_nat
  no x1 = match no, x1 with no, None -> true
    | None, Some x -> less_nat zero_nata x
    | Some x, Some y -> less_nat one_nata (minus_nata y x);;

let rec cproper_interval_nata x = proper_interval_nat x;;

type 'a cproper_interval =
  {ccompare_cproper_interval : 'a ccompare;
    cproper_interval : 'a option -> 'a option -> bool};;
let cproper_interval _A = _A.cproper_interval;;

let cproper_interval_nat =
  ({ccompare_cproper_interval = ccompare_nat;
     cproper_interval = cproper_interval_nata}
    : nat cproper_interval);;

let rec equal_order x0 x1 = match x0, x1 with Lt, Gt -> false
                      | Gt, Lt -> false
                      | Eqa, Gt -> false
                      | Gt, Eqa -> false
                      | Eqa, Lt -> false
                      | Lt, Eqa -> false
                      | Gt, Gt -> true
                      | Lt, Lt -> true
                      | Eqa, Eqa -> true;;

type ('a, 'b) generator = Generator of (('b -> bool) * ('b -> 'a * 'b));;

let rec generator (Generator x) = x;;

let rec has_next g = fst (generator g);;

let rec next g = snd (generator g);;

let rec sorted_list_subset_fusion
  less eq g1 g2 s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             has_next g2 s2 &&
               (let (y, s2a) = next g2 s2 in
                 (if eq x y then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                   else less y x &&
                          sorted_list_subset_fusion less eq g1 g2 s1 s2a)))
      else true);;

let rec list_all_fusion
  g p s =
    (if has_next g s
      then (let (x, sa) = next g s in p x && list_all_fusion g p sa)
      else true);;

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

let rec rbt_keys_next
  = function ((k, t) :: kts, Empty) -> (k, (kts, t))
    | (kts, Branch (c, l, k, v, r)) -> rbt_keys_next ((k, r) :: kts, l);;

let rec rbt_has_next = function ([], Empty) -> false
                       | (vb :: vc, va) -> true
                       | (v, Branch (vb, vc, vd, ve, vf)) -> true;;

let rbt_keys_generator :
  ('a, (('a * ('a, 'b) rbt) list * ('a, 'b) rbt)) generator
  = Generator (rbt_has_next, rbt_keys_next);;

let rec lt_of_comp
  acomp x y = (match acomp x y with Eqa -> false | Lt -> true | Gt -> false);;

type ('b, 'a) mapping_rbt = Mapping_RBTa of ('b, 'a) rbt;;

type 'a set_dlist = Abs_dlist of 'a list;;

type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;;

let rec list_of_dlist _A (Abs_dlist x) = x;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec dlist_all _A x xc = list_all x (list_of_dlist _A xc);;

let rec impl_ofa _B (Mapping_RBTa x) = x;;

let rec rbt_init x = ([], x);;

let rec init _A xa = rbt_init (impl_ofa _A xa);;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec collect _A
  p = (match cEnum _A with None -> Collect_set p
        | Some (enum, _) -> Set_Monad (filtera p enum));;

let rec list_member
  equal x1 y = match equal, x1, y with equal, [], y -> false
    | equal, x :: xs, y -> equal x y || list_member equal xs y;;

let rec the (Some x2) = x2;;

let rec memberc _A xa = list_member (the (ceq _A)) (list_of_dlist _A xa);;

let rec eq _A a b = equal _A a b;;

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> eq _A x2 y2
                           | None, None -> true;;

let rec rbt_comp_lookup
  c x1 k = match c, x1, k with c, Empty, k -> None
    | c, Branch (uu, l, x, y, r), k ->
        (match c k x with Eqa -> Some y | Lt -> rbt_comp_lookup c l k
          | Gt -> rbt_comp_lookup c r k);;

let rec lookupb _A t k = rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A t) k;;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec memberb _A t x = equal_optiona equal_unit (lookupb _A t x) (Some ());;

let rec member (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Set_Monad xs ->
      (match ceq _A1
        with None ->
          failwith "member Set_Monad: ceq = None"
            (fun _ -> member (_A1, _A2) x (Set_Monad xs))
        | Some eq -> list_member eq xs x)
    | xa, Complement x -> not (member (_A1, _A2) xa x)
    | x, RBT_set rbt -> memberb _A2 rbt x
    | x, DList_set dxs -> memberc _A1 dxs x
    | x, Collect_set a -> a x;;

let rec less_eq_set (_A1, _A2, _A3)
  x0 b = match x0, b with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A3
        with None ->
          failwith "subset RBT_set RBT_set: ccompare = None"
            (fun _ -> less_eq_set (_A1, _A2, _A3) (RBT_set rbt1) (RBT_set rbt2))
        | Some c ->
          (match ceq _A2
            with None ->
              sorted_list_subset_fusion (lt_of_comp c)
                (fun x y -> equal_order (c x y) Eqa) rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)
            | Some eq ->
              sorted_list_subset_fusion (lt_of_comp c) eq rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)))
    | Complement a1, Complement a2 -> less_eq_set (_A1, _A2, _A3) a2 a1
    | Collect_set p, Complement a ->
        less_eq_set (_A1, _A2, _A3) a (collect _A1 (fun x -> not (p x)))
    | RBT_set rbt, b ->
        (match ccompare _A3
          with None ->
            failwith "subset RBT_set1: ccompare = None"
              (fun _ -> less_eq_set (_A1, _A2, _A3) (RBT_set rbt) b)
          | Some _ ->
            list_all_fusion rbt_keys_generator (fun x -> member (_A2, _A3) x b)
              (init _A3 rbt))
    | DList_set dxs, c ->
        (match ceq _A2
          with None ->
            failwith "subset DList_set1: ceq = None"
              (fun _ -> less_eq_set (_A1, _A2, _A3) (DList_set dxs) c)
          | Some _ -> dlist_all _A2 (fun x -> member (_A2, _A3) x c) dxs)
    | Set_Monad xs, c -> list_all (fun x -> member (_A2, _A3) x c) xs;;

let rec equal_seta (_A1, _A2, _A3, _A4)
  a b = less_eq_set (_A1, _A2, _A3) a b && less_eq_set (_A1, _A2, _A3) b a;;

let rec equal_set (_A1, _A2, _A3, _A4) =
  ({equal = equal_seta (_A1, _A2, _A3, _A4)} : 'a set equal);;

let rec equal_color x0 x1 = match x0, x1 with R, B -> false
                      | B, R -> false
                      | B, B -> true
                      | R, R -> true;;

let rec color_of = function Empty -> B
                   | Branch (c, uu, uv, uw, ux) -> c;;

let rec rbt_recolor
  = function
    Branch (R, t1, k, v, t2) ->
      (if equal_color (color_of t1) B && equal_color (color_of t2) B
        then Branch (B, t1, k, v, t2) else Branch (R, t1, k, v, t2))
    | Empty -> Empty
    | Branch (B, va, vb, vc, vd) -> Branch (B, va, vb, vc, vd);;

let rec bh_le
  x0 t2 = match x0, t2 with Empty, t2 -> true
    | Branch (R, l1, a1, b1, r1), t2 -> bh_le l1 t2
    | Branch (B, l1, a1, b1, r1), Empty -> false
    | Branch (B, l1, a1, b1, r1), Branch (R, l2, a2, b2, r2) ->
        bh_le (Branch (B, l1, a1, b1, r1)) l2
    | Branch (B, l1, a1, b1, r1), Branch (B, l2, a2, b2, r2) -> bh_le l1 l2;;

let rec baliR
  t1 a x2 = match t1, a, x2 with
    t1, a, Branch (R, t2, b, (), Branch (R, t3, c, (), t4)) ->
      Branch (R, Branch (B, t1, a, (), t2), b, (), Branch (B, t3, c, (), t4))
    | t1, a, Branch (R, Branch (R, t2, b, (), t3), c, (), Empty) ->
        Branch
          (R, Branch (B, t1, a, (), t2), b, (), Branch (B, t3, c, (), Empty))
    | t1, a,
        Branch (R, Branch (R, t2, b, (), t3), c, (), Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, t1, a, (), t2), b, (),
               Branch (B, t3, c, (), Branch (B, va, vb, vc, vd)))
    | t1, a, Empty -> Branch (B, t1, a, (), Empty)
    | t1, a, Branch (B, va, vb, vc, vd) ->
        Branch (B, t1, a, (), Branch (B, va, vb, vc, vd))
    | t1, a, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, t1, a, (), Branch (v, Empty, vb, vc, Empty))
    | t1, a, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, t1, a, (), Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | t1, a, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, t1, a, (), Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | t1, a,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, t1, a, (),
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)));;

let rec rbt_joinRa
  l x r =
    (if bh_le l r then Branch (R, l, x, (), r)
      else (match l
             with Branch (R, la, xa, (), ra) ->
               Branch (R, la, xa, (), rbt_joinRa ra x r)
             | Branch (B, la, xa, (), ra) -> baliR la xa (rbt_joinRa ra x r)));;

let rec baliL
  x0 c t4 = match x0, c, t4 with
    Branch (R, Branch (R, t1, a, (), t2), b, (), t3), c, t4 ->
      Branch (R, Branch (B, t1, a, (), t2), b, (), Branch (B, t3, c, (), t4))
    | Branch (R, Empty, a, (), Branch (R, t2, b, (), t3)), c, t4 ->
        Branch
          (R, Branch (B, Empty, a, (), t2), b, (), Branch (B, t3, c, (), t4))
    | Branch (R, Branch (B, va, vb, vc, vd), a, (), Branch (R, t2, b, (), t3)),
        c, t4
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), a, (), t2), b, (),
               Branch (B, t3, c, (), t4))
    | Empty, a, t2 -> Branch (B, Empty, a, (), t2)
    | Branch (B, va, vb, vc, vd), a, t2 ->
        Branch (B, Branch (B, va, vb, vc, vd), a, (), t2)
    | Branch (v, Empty, vb, vc, Empty), a, t2 ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), a, (), t2)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, t2 ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, (), t2)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, t2 ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, (), t2)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        a, t2
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               a, (), t2);;

let rec rbt_joinLa
  l x r =
    (if bh_le r l then Branch (R, l, x, (), r)
      else (match r
             with Branch (R, la, xa, (), ra) ->
               Branch (R, rbt_joinLa l x la, xa, (), ra)
             | Branch (B, la, xa, (), ra) -> baliL (rbt_joinLa l x la) xa ra));;

let rec painta c x1 = match c, x1 with c, Empty -> Empty
                 | c, Branch (uu, l, a, (), r) -> Branch (c, l, a, (), r);;

let rec rbt_joina
  l x r =
    (if not (bh_le l r) then painta B (rbt_joinRa l x r)
      else (if not (bh_le r l) then painta B (rbt_joinLa l x r)
             else Branch (B, l, x, (), r)));;

let rec split_comp
  comp x1 k = match comp, x1, k with comp, Empty, k -> (Empty, (false, Empty))
    | comp, Branch (uu, l, a, (), r), x ->
        (match comp x a with Eqa -> (l, (true, r))
          | Lt ->
            (let (l1, (b, l2)) = split_comp comp l x in
              (l1, (b, rbt_joina l2 a r)))
          | Gt ->
            (let (r1, (b, r2)) = split_comp comp r x in
              (rbt_joina l a r1, (b, r2))));;

let rec bh_lt
  k x1 = match k, x1 with k, Empty -> Z.lt Z.zero k
    | k, Branch (R, l, a, b, r) -> bh_lt k l
    | k, Branch (B, l, a, b, r) ->
        (if Z.leq k Z.zero then false else bh_lt (Z.sub k (Z.of_int 1)) l);;

let rec small_rbta t = bh_lt (Z.of_int 6) t;;

let rec is_emptyb
  t = (match t with Empty -> true | Branch (_, _, _, _, _) -> false);;

let rec split_min
  = function Empty -> failwith "undefined"
    | Branch (uu, l, a, uv, r) ->
        (if is_emptyb l then (a, r)
          else (let (m, la) = split_min l in (m, rbt_joina la a r)));;

let rec rbt_join2a
  l r = (if is_emptyb r then l
          else (let (a, b) = split_min r in rbt_joina l a b));;

let rec flip_rbt t1 t2 = not (bh_le t1 t2);;

let rec suc n = plus_nata n one_nata;;

let rec length_tailrec x0 n = match x0, n with [], n -> n
                         | x :: xs, n -> length_tailrec xs (suc n);;

let rec size_lista xs = length_tailrec xs zero_nata;;

let rec nat_of_integer k = Nat (ed_max_integer Z.zero k);;

let rec map_prod f g (a, b) = (f a, g b);;

let rec divmod_nat
  m n = (let k = integer_of_nat m in
         let l = integer_of_nat n in
          map_prod nat_of_integer nat_of_integer
            (if Z.equal k Z.zero then (Z.zero, Z.zero)
              else (if Z.equal l Z.zero then (Z.zero, k)
                     else (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else
                            Z.div_rem (Z.abs k) (Z.abs l))
                            k l)));;

let rec apfst f (x, y) = (f x, y);;

let rec rbtreeify_g
  n kvs =
    (if equal_nata n zero_nata || equal_nata n one_nata then (Empty, kvs)
      else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
             (if equal_nata r zero_nata
               then (let (t1, (k, v) :: kvsa) = rbtreeify_g na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa))
               else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa)))))
and rbtreeify_f
  n kvs =
    (if equal_nata n zero_nata then (Empty, kvs)
      else (if equal_nata n one_nata
             then (let (k, v) :: kvsa = kvs in
                    (Branch (R, Empty, k, v, Empty), kvsa))
             else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
                    (if equal_nata r zero_nata
                      then (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_g na kvsa))
                      else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_f na kvsa))))));;

let rec rbtreeify kvs = fst (rbtreeify_g (suc (size_lista kvs)) kvs);;

let rec gen_entries
  kvts x1 = match kvts, x1 with [], Empty -> []
    | (kv, t) :: kvts, Empty -> kv :: gen_entries kvts t
    | kvts, Branch (c, l, k, v, r) -> gen_entries (((k, v), r) :: kvts) l;;

let rec entries x = gen_entries [] x;;

let rec inter_comp
  comp t1 t2 =
    (let (t1a, t2a) = (if flip_rbt t1 t2 then (t2, t1) else (t1, t2)) in
      (if small_rbta t1a
        then rbtreeify
               (filtera
                 (fun (k, _) ->
                   equal_optiona equal_unit (rbt_comp_lookup comp t2a k)
                     (Some ()))
                 (entries t1a))
        else (match t2a with Empty -> Empty
               | Branch (_, l2, a, (), r2) ->
                 (let (l1, (ain, r1)) = split_comp comp t1a a in
                  let l = inter_comp comp l1 l2 in
                  let r = inter_comp comp r1 r2 in
                   (if ain then rbt_joina l a r else rbt_join2a l r)))));;

let rec rbt_inter_rbt_join2 _A
  xb xc =
    Mapping_RBTa
      (rbt_recolor
        (inter_comp (the (ccompare _A)) (impl_ofa _A xb) (impl_ofa _A xc)));;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_comp_ins
  c f k v x4 = match c, f, k, v, x4 with
    c, f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | c, f, k, v, Branch (B, l, x, y, r) ->
        (match c k x with Eqa -> Branch (B, l, x, f k y v, r)
          | Lt -> balance (rbt_comp_ins c f k v l) x y r
          | Gt -> balance l x y (rbt_comp_ins c f k v r))
    | c, f, k, v, Branch (R, l, x, y, r) ->
        (match c k x with Eqa -> Branch (R, l, x, f k y v, r)
          | Lt -> Branch (R, rbt_comp_ins c f k v l, x, y, r)
          | Gt -> Branch (R, l, x, y, rbt_comp_ins c f k v r));;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);;

let rec rbt_comp_insert c = rbt_comp_insert_with_key c (fun _ _ nv -> nv);;

let rec folda
  f xa1 x = match f, xa1, x with f, Empty, x -> x
    | f, Branch (c, lt, k, v, rt), x -> folda f rt (f k v (folda f lt x));;

let rec union_comp
  comp t1 t2 =
    (let (t1a, t2a) = (if flip_rbt t1 t2 then (t2, t1) else (t1, t2)) in
      (if small_rbta t1a then folda (rbt_comp_insert comp) t1a t2a
        else (match t2a with Empty -> t1a
               | Branch (_, l2, a, (), r2) ->
                 (let (l1, (_, r1)) = split_comp comp t1a a in
                   rbt_joina (union_comp comp l1 l2) a
                     (union_comp comp r1 r2)))));;

let rec rbt_union_rbt_join2 _A
  xb xc =
    Mapping_RBTa
      (rbt_recolor
        (union_comp (the (ccompare _A)) (impl_ofa _A xb) (impl_ofa _A xc)));;

let rec uminus_set = function Complement b -> b
                     | Collect_set p -> Collect_set (fun x -> not (p x))
                     | a -> Complement a;;

let rec insertb _A
  xc xd xe =
    Mapping_RBTa (rbt_comp_insert (the (ccompare _A)) xc xd (impl_ofa _A xe));;

let rec list_insert
  equal x xs = (if list_member equal xs x then xs else x :: xs);;

let rec inserta _A
  xb xc = Abs_dlist (list_insert (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec fold f x1 s = match f, x1, s with f, [], s -> s
               | f, x :: xs, s -> fold f xs (f x s);;

let rec foldc _A x xc = fold x (list_of_dlist _A xc);;

let rec union _A = foldc _A (inserta _A);;

let rec is_none = function None -> true
                  | Some x -> false;;

let rec inter_list _A
  xb xc =
    Mapping_RBTa
      (fold (fun k -> rbt_comp_insert (the (ccompare _A)) k ())
        (filtera
          (fun x ->
            not (is_none
                  (rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xb) x)))
          xc)
        Empty);;

let rec filtere _A
  xb xc = Mapping_RBTa (rbtreeify (filtera xb (entries (impl_ofa _A xc))));;

let rec filterd _A xb xc = Abs_dlist (filtera xb (list_of_dlist _A xc));;

let rec comp f g = (fun x -> f (g x));;

let rec inf_seta (_A1, _A2)
  g ga = match g, ga with
    RBT_set t1, RBT_set t2 ->
      (match ccompare _A2
        with None ->
          failwith "inter RBT_set RBT_set: ccompare = None"
            (fun _ -> inf_seta (_A1, _A2) (RBT_set t1) (RBT_set t2))
        | Some _ -> RBT_set (rbt_inter_rbt_join2 _A2 t1 t2))
    | RBT_set rbt1, Set_Monad xs ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set Set_Monad: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
          | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | Set_Monad xs, RBT_set rbt1 ->
        (match ccompare _A2
          with None ->
            failwith "inter Set_Monad RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
          | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | Set_Monad xs, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad DList_set: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (Set_Monad xs) (DList_set dxs2))
          | Some eq -> DList_set (filterd _A1 (list_member eq xs) dxs2))
    | Set_Monad xs1, Set_Monad xs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad Set_Monad: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (Set_Monad xs1) (Set_Monad xs2))
          | Some eq -> Set_Monad (filtera (list_member eq xs2) xs1))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set DList_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter RBT_set DList_set: ceq = None"
                  (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | DList_set dxs1, Set_Monad xs ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set Set_Monad: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) (Set_Monad xs))
          | Some eq -> DList_set (filterd _A1 (list_member eq xs) dxs1))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set DList_set: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (filterd _A1 (memberc _A1 dxs2) dxs1))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "inter DList_set RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs) (RBT_set rbt))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter DList_set RBT_set: ceq = None"
                  (fun _ -> inf_seta (_A1, _A2) (DList_set dxs) (RBT_set rbt))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | Complement ba, Complement b -> Complement (sup_seta (_A1, _A2) ba b)
    | g, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set2: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) g (RBT_set rbt2))
          | Some _ ->
            RBT_set
              (filtere _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt2))
    | RBT_set rbt1, g ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set1: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) g)
          | Some _ ->
            RBT_set
              (filtere _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt1))
    | h, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set2: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) h (DList_set dxs2))
          | Some _ ->
            DList_set (filterd _A1 (fun x -> member (_A1, _A2) x h) dxs2))
    | DList_set dxs1, h ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set1: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) h)
          | Some _ ->
            DList_set (filterd _A1 (fun x -> member (_A1, _A2) x h) dxs1))
    | i, Set_Monad xs -> Set_Monad (filtera (fun x -> member (_A1, _A2) x i) xs)
    | Set_Monad xs, i -> Set_Monad (filtera (fun x -> member (_A1, _A2) x i) xs)
    | j, Collect_set a -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
    | Collect_set a, j -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
and sup_seta (_A1, _A2)
  ba b = match ba, b with
    RBT_set t1, RBT_set t2 ->
      (match ccompare _A2
        with None ->
          failwith "union RBT_set RBT_set: ccompare = None"
            (fun _ -> sup_seta (_A1, _A2) (RBT_set t1) (RBT_set t2))
        | Some _ -> RBT_set (rbt_union_rbt_join2 _A2 t1 t2))
    | ba, Complement b -> Complement (inf_seta (_A1, _A2) (uminus_set ba) b)
    | Complement ba, b -> Complement (inf_seta (_A1, _A2) ba (uminus_set b))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set DList_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union RBT_set DList_set: ceq = None"
                  (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "union DList_set RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union DList_set RBT_set: ceq = None"
                  (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union DList_set DList_set: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (union _A1 dxs1 dxs2))
    | Set_Monad zs, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "union Set_Monad RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (Set_Monad zs) (RBT_set rbt2))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt2))
    | RBT_set rbt1, Set_Monad zs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set Set_Monad: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad zs))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt1))
    | Set_Monad ws, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union Set_Monad DList_set: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (Set_Monad ws) (DList_set dxs2))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs2))
    | DList_set dxs1, Set_Monad ws ->
        (match ceq _A1
          with None ->
            failwith "union DList_set Set_Monad: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (DList_set dxs1) (Set_Monad ws))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs1))
    | Set_Monad xs, Set_Monad ys -> Set_Monad (xs @ ys)
    | b, Collect_set a -> Collect_set (fun x -> a x || member (_A1, _A2) x b)
    | Collect_set a, b -> Collect_set (fun x -> a x || member (_A1, _A2) x b);;

let rec inf_set (_A1, _A2) = ({inf = inf_seta (_A1, _A2)} : 'a set inf);;

let rec sup_set (_A1, _A2) = ({sup = sup_seta (_A1, _A2)} : 'a set sup);;

let rec less_set (_A1, _A2, _A3)
  a b = less_eq_set (_A1, _A2, _A3) a b &&
          not (less_eq_set (_A1, _A2, _A3) b a);;

let rec ord_set (_A1, _A2, _A3) =
  ({less_eq = less_eq_set (_A1, _A2, _A3); less = less_set (_A1, _A2, _A3)} :
    'a set ord);;

let rec preorder_set (_A1, _A2, _A3) =
  ({ord_preorder = (ord_set (_A1, _A2, _A3))} : 'a set preorder);;

let rec order_set (_A1, _A2, _A3) =
  ({preorder_order = (preorder_set (_A1, _A2, _A3))} : 'a set order);;

let rec semilattice_sup_set (_A1, _A2, _A3) =
  ({sup_semilattice_sup = (sup_set (_A2, _A3));
     order_semilattice_sup = (order_set (_A1, _A2, _A3))}
    : 'a set semilattice_sup);;

let rec semilattice_inf_set (_A1, _A2, _A3) =
  ({inf_semilattice_inf = (inf_set (_A2, _A3));
     order_semilattice_inf = (order_set (_A1, _A2, _A3))}
    : 'a set semilattice_inf);;

let rec lattice_set (_A1, _A2, _A3) =
  ({semilattice_inf_lattice = (semilattice_inf_set (_A1, _A2, _A3));
     semilattice_sup_lattice = (semilattice_sup_set (_A1, _A2, _A3))}
    : 'a set lattice);;

let rec list_all2_fusion
  p g1 g2 s1 s2 =
    (if has_next g1 s1
      then has_next g2 s2 &&
             (let (x, s1a) = next g1 s1 in
              let (y, s2a) = next g2 s2 in
               p x y && list_all2_fusion p g1 g2 s1a s2a)
      else not (has_next g2 s2));;

let rec set_eq (_A1, _A2, _A3)
  a b = match a, b with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A3
        with None ->
          failwith "set_eq RBT_set RBT_set: ccompare = None"
            (fun _ -> set_eq (_A1, _A2, _A3) (RBT_set rbt1) (RBT_set rbt2))
        | Some c ->
          (match ceq _A2
            with None ->
              list_all2_fusion (fun x y -> equal_order (c x y) Eqa)
                rbt_keys_generator rbt_keys_generator (init _A3 rbt1)
                (init _A3 rbt2)
            | Some eq ->
              list_all2_fusion eq rbt_keys_generator rbt_keys_generator
                (init _A3 rbt1) (init _A3 rbt2)))
    | Complement a, Complement b -> set_eq (_A1, _A2, _A3) a b
    | a, b ->
        less_eq_set (_A1, _A2, _A3) a b && less_eq_set (_A1, _A2, _A3) b a;;

let rec ceq_seta (_A1, _A2, _A3)
  = (match ceq _A2 with None -> None
      | Some _ -> Some (set_eq (_A1, _A2, _A3)));;

let rec ceq_set (_A1, _A2, _A3) =
  ({ceq = ceq_seta (_A1, _A2, _A3)} : 'a set ceq);;

let set_impl_seta : ('a set, set_impla) phantom = Phantom Set_Choose;;

let set_impl_set = ({set_impl = set_impl_seta} : 'a set set_impl);;

let rec of_phantom (Phantom x) = x;;

let rec finite_UNIV_seta _A = Phantom (of_phantom (finite_UNIV _A));;

let rec finite_UNIV_set _A =
  ({finite_UNIV = finite_UNIV_seta _A} : 'a set finite_UNIV);;

let rec set_less_eq_aux_Compl_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (if has_next g2 s2
             then (let (x, s1a) = next g1 s1 in
                   let (y, s2a) = next g2 s2 in
                    (if less x y
                      then proper_interval ao (Some x) ||
                             set_less_eq_aux_Compl_fusion less proper_interval
                               g1 g2 (Some x) s1a s2
                      else (if less y x
                             then proper_interval ao (Some y) ||
                                    set_less_eq_aux_Compl_fusion less
                                      proper_interval g1 g2 (Some y) s1 s2a
                             else proper_interval ao (Some y))))
             else true)
      else true);;

let rec compl_set_less_eq_aux_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             (if has_next g2 s2
               then (let (y, s2a) = next g2 s2 in
                      (if less x y
                        then not (proper_interval ao (Some x)) &&
                               compl_set_less_eq_aux_fusion less proper_interval
                                 g1 g2 (Some x) s1a s2
                        else (if less y x
                               then not (proper_interval ao (Some y)) &&
                                      compl_set_less_eq_aux_fusion less
proper_interval g1 g2 (Some y) s1 s2a
                               else not (proper_interval ao (Some y)))))
               else not (proper_interval ao (Some x)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Some x) s1a s2))
      else (if has_next g2 s2
             then (let (y, s2a) = next g2 s2 in
                    not (proper_interval ao (Some y)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Some y) s1 s2a)
             else not (proper_interval ao None)));;

let rec set_less_eq_aux_Compl
  less proper_interval ao xs ys = match less, proper_interval, ao, xs, ys with
    less, proper_interval, ao, [], ys -> true
    | less, proper_interval, ao, xs, [] -> true
    | less, proper_interval, ao, x :: xs, y :: ys ->
        (if less x y
          then proper_interval ao (Some x) ||
                 set_less_eq_aux_Compl less proper_interval (Some x) xs
                   (y :: ys)
          else (if less y x
                 then proper_interval ao (Some y) ||
                        set_less_eq_aux_Compl less proper_interval (Some y)
                          (x :: xs) ys
                 else proper_interval ao (Some y)));;

let rec compl_set_less_eq_aux
  less proper_interval ao x3 x4 = match less, proper_interval, ao, x3, x4 with
    less, proper_interval, ao, [], [] -> not (proper_interval ao None)
    | less, proper_interval, ao, [], y :: ys ->
        not (proper_interval ao (Some y)) &&
          compl_set_less_eq_aux less proper_interval (Some y) [] ys
    | less, proper_interval, ao, x :: xs, [] ->
        not (proper_interval ao (Some x)) &&
          compl_set_less_eq_aux less proper_interval (Some x) xs []
    | less, proper_interval, ao, x :: xs, y :: ys ->
        (if less x y
          then not (proper_interval ao (Some x)) &&
                 compl_set_less_eq_aux less proper_interval (Some x) xs
                   (y :: ys)
          else (if less y x
                 then not (proper_interval ao (Some y)) &&
                        compl_set_less_eq_aux less proper_interval (Some y)
                          (x :: xs) ys
                 else not (proper_interval ao (Some y))));;

let rec lexord_eq_fusion
  less g1 g2 s1 s2 =
    (if has_next g1 s1
      then has_next g2 s2 &&
             (let (x, s1a) = next g1 s1 in
              let (y, s2a) = next g2 s2 in
               less x y ||
                 not (less y x) && lexord_eq_fusion less g1 g2 s1a s2a)
      else true);;

let rec remdups_sorted
  less x1 = match less, x1 with less, [] -> []
    | less, [x] -> [x]
    | less, x :: y :: xs ->
        (if less x y then x :: remdups_sorted less (y :: xs)
          else remdups_sorted less (y :: xs));;

let rec quicksort_acc
  less ac x2 = match less, ac, x2 with less, ac, [] -> ac
    | less, ac, [x] -> x :: ac
    | less, ac, x :: v :: va -> quicksort_part less ac x [] [] [] (v :: va)
and quicksort_part
  less ac x lts eqs gts xa6 = match less, ac, x, lts, eqs, gts, xa6 with
    less, ac, x, lts, eqs, gts, [] ->
      quicksort_acc less (eqs @ x :: quicksort_acc less ac gts) lts
    | less, ac, x, lts, eqs, gts, z :: zs ->
        (if less x z then quicksort_part less ac x lts eqs (z :: gts) zs
          else (if less z x then quicksort_part less ac x (z :: lts) eqs gts zs
                 else quicksort_part less ac x lts (z :: eqs) gts zs));;

let rec quicksort less = quicksort_acc less [];;

let rec gen_keys kts x1 = match kts, x1 with [], Empty -> []
                   | (k, t) :: kts, Empty -> k :: gen_keys kts t
                   | kts, Branch (c, l, k, v, r) -> gen_keys ((k, r) :: kts) l;;

let rec keysa x = gen_keys [] x;;

let rec keysb _A xa = keysa (impl_ofa _A xa);;

let rec csorted_list_of_set (_A1, _A2)
  = function
    Set_Monad xs ->
      (match ccompare _A2
        with None ->
          failwith "csorted_list_of_set Set_Monad: ccompare = None"
            (fun _ -> csorted_list_of_set (_A1, _A2) (Set_Monad xs))
        | Some c -> remdups_sorted (lt_of_comp c) (quicksort (lt_of_comp c) xs))
    | DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "csorted_list_of_set DList_set: ceq = None"
              (fun _ -> csorted_list_of_set (_A1, _A2) (DList_set dxs))
          | Some _ ->
            (match ccompare _A2
              with None ->
                failwith "csorted_list_of_set DList_set: ccompare = None"
                  (fun _ -> csorted_list_of_set (_A1, _A2) (DList_set dxs))
              | Some c -> quicksort (lt_of_comp c) (list_of_dlist _A1 dxs)))
    | RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "csorted_list_of_set RBT_set: ccompare = None"
              (fun _ -> csorted_list_of_set (_A1, _A2) (RBT_set rbt))
          | Some _ -> keysb _A2 rbt);;

let rec emptyc _A = Mapping_RBTa Empty;;

let rec emptyb _A = Abs_dlist [];;

let rec set_empty_choose (_A1, _A2)
  = (match ccompare _A2
      with None ->
        (match ceq _A1 with None -> Set_Monad []
          | Some _ -> DList_set (emptyb _A1))
      | Some _ -> RBT_set (emptyc _A2));;

let rec set_empty (_A1, _A2)
  = function Set_Collect -> Collect_set (fun _ -> false)
    | Set_DList -> DList_set (emptyb _A1)
    | Set_RBT -> RBT_set (emptyc _A2)
    | Set_Monada -> Set_Monad []
    | Set_Choose -> set_empty_choose (_A1, _A2);;

let rec bot_set (_A1, _A2, _A3)
  = set_empty (_A1, _A2) (of_phantom (set_impl _A3));;

let rec top_set (_A1, _A2, _A3) = uminus_set (bot_set (_A1, _A2, _A3));;

let rec le_of_comp
  acomp x y = (match acomp x y with Eqa -> true | Lt -> true | Gt -> false);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec lexordp_eq
  less xs ys = match less, xs, ys with less, [], ys -> true
    | less, xs, [] -> null xs
    | less, x :: xs, y :: ys ->
        less x y || not (less y x) && lexordp_eq less xs ys;;

let rec finite (_A1, _A2, _A3)
  = function
    Collect_set p ->
      of_phantom (finite_UNIV _A1) ||
        failwith "finite Collect_set"
          (fun _ -> finite (_A1, _A2, _A3) (Collect_set p))
    | Set_Monad xs -> true
    | Complement a ->
        (if of_phantom (finite_UNIV _A1) then true
          else (if finite (_A1, _A2, _A3) a then false
                 else failwith "finite Complement: infinite set"
                        (fun _ -> finite (_A1, _A2, _A3) (Complement a))))
    | RBT_set rbt ->
        (match ccompare _A3
          with None ->
            failwith "finite RBT_set: ccompare = None"
              (fun _ -> finite (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> true)
    | DList_set dxs ->
        (match ceq _A2
          with None ->
            failwith "finite DList_set: ceq = None"
              (fun _ -> finite (_A1, _A2, _A3) (DList_set dxs))
          | Some _ -> true);;

let rec set_less_aux_Compl_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             (if has_next g2 s2
               then (let (y, s2a) = next g2 s2 in
                      (if less x y
                        then proper_interval ao (Some x) ||
                               set_less_aux_Compl_fusion less proper_interval g1
                                 g2 (Some x) s1a s2
                        else (if less y x
                               then proper_interval ao (Some y) ||
                                      set_less_aux_Compl_fusion less
proper_interval g1 g2 (Some y) s1 s2a
                               else proper_interval ao (Some y))))
               else proper_interval ao (Some x) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Some x) s1a s2))
      else (if has_next g2 s2
             then (let (y, s2a) = next g2 s2 in
                    proper_interval ao (Some y) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Some y) s1 s2a)
             else proper_interval ao None));;

let rec compl_set_less_aux_fusion
  less proper_interval g1 g2 ao s1 s2 =
    has_next g1 s1 &&
      (has_next g2 s2 &&
        (let (x, s1a) = next g1 s1 in
         let (y, s2a) = next g2 s2 in
          (if less x y
            then not (proper_interval ao (Some x)) &&
                   compl_set_less_aux_fusion less proper_interval g1 g2 (Some x)
                     s1a s2
            else (if less y x
                   then not (proper_interval ao (Some y)) &&
                          compl_set_less_aux_fusion less proper_interval g1 g2
                            (Some y) s1 s2a
                   else not (proper_interval ao (Some y))))));;

let rec set_less_aux_Compl
  less proper_interval ao x3 x4 = match less, proper_interval, ao, x3, x4 with
    less, proper_interval, ao, [], [] -> proper_interval ao None
    | less, proper_interval, ao, [], y :: ys ->
        proper_interval ao (Some y) ||
          set_less_aux_Compl less proper_interval (Some y) [] ys
    | less, proper_interval, ao, x :: xs, [] ->
        proper_interval ao (Some x) ||
          set_less_aux_Compl less proper_interval (Some x) xs []
    | less, proper_interval, ao, x :: xs, y :: ys ->
        (if less x y
          then proper_interval ao (Some x) ||
                 set_less_aux_Compl less proper_interval (Some x) xs (y :: ys)
          else (if less y x
                 then proper_interval ao (Some y) ||
                        set_less_aux_Compl less proper_interval (Some y)
                          (x :: xs) ys
                 else proper_interval ao (Some y)));;

let rec compl_set_less_aux
  less proper_interval ao xs ys = match less, proper_interval, ao, xs, ys with
    less, proper_interval, ao, [], ys -> false
    | less, proper_interval, ao, xs, [] -> false
    | less, proper_interval, ao, x :: xs, y :: ys ->
        (if less x y
          then not (proper_interval ao (Some x)) &&
                 compl_set_less_aux less proper_interval (Some x) xs (y :: ys)
          else (if less y x
                 then not (proper_interval ao (Some y)) &&
                        compl_set_less_aux less proper_interval (Some y)
                          (x :: xs) ys
                 else not (proper_interval ao (Some y))));;

let rec lexord_fusion
  less g1 g2 s1 s2 =
    (if has_next g1 s1
      then (if has_next g2 s2
             then (let (x, s1a) = next g1 s1 in
                   let (y, s2a) = next g2 s2 in
                    less x y ||
                      not (less y x) && lexord_fusion less g1 g2 s1a s2a)
             else false)
      else has_next g2 s2);;

let rec lexordp
  less xs ys = match less, xs, ys with less, [], ys -> not (null ys)
    | less, xs, [] -> false
    | less, x :: xs, y :: ys ->
        less x y || not (less y x) && lexordp less xs ys;;

let rec comp_of_ords
  le lt x y = (if lt x y then Lt else (if le x y then Eqa else Gt));;

let rec ccompare_seta (_A1, _A2, _A3, _A4)
  = (match ccompare _A3.ccompare_cproper_interval with None -> None
      | Some _ ->
        Some (comp_of_ords (cless_eq_set (_A1, _A2, _A3, _A4))
               (cless_set (_A1, _A2, _A3, _A4))))
and cless_set (_A1, _A2, _A3, _A4)
  a b = match a, b with
    Complement (RBT_set rbt1), RBT_set rbt2 ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "cless_set (Complement RBT_set) RBT_set: ccompare = None"
            (fun _ ->
              cless_set (_A1, _A2, _A3, _A4) (Complement (RBT_set rbt1))
                (RBT_set rbt2))
        | Some c ->
          finite (_A1, _A2, _A3.ccompare_cproper_interval)
            (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
            compl_set_less_aux_fusion (lt_of_comp c) (cproper_interval _A3)
              rbt_keys_generator rbt_keys_generator None
              (init _A3.ccompare_cproper_interval rbt1)
              (init _A3.ccompare_cproper_interval rbt2))
    | RBT_set rbt1, Complement (RBT_set rbt2) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set RBT_set (Complement RBT_set): ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (RBT_set rbt1)
                  (Complement (RBT_set rbt2)))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                  (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
              then set_less_aux_Compl_fusion (lt_of_comp c)
                     (cproper_interval _A3) rbt_keys_generator
                     rbt_keys_generator None
                     (init _A3.ccompare_cproper_interval rbt1)
                     (init _A3.ccompare_cproper_interval rbt2)
              else true))
    | RBT_set rbta, RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set RBT_set RBT_set: ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (RBT_set rbta) (RBT_set rbt))
          | Some c ->
            lexord_fusion (fun x y -> lt_of_comp c y x) rbt_keys_generator
              rbt_keys_generator (init _A3.ccompare_cproper_interval rbta)
              (init _A3.ccompare_cproper_interval rbt))
    | Complement a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement Complement: ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (Complement a) (Complement b))
          | Some _ -> lt_of_comp (the (ccompare_seta (_A1, _A2, _A3, _A4))) b a)
    | Complement a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement1: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) (Complement a) b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then finite (_A1, _A2, _A3.ccompare_cproper_interval)
                     (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
                     compl_set_less_aux (lt_of_comp c) (cproper_interval _A3)
                       None
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         a)
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         b)
              else failwith "cless_set Complement1: infinite set"
                     (fun _ ->
                       cless_set (_A1, _A2, _A3, _A4) (Complement a) b)))
    | a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement2: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) a (Complement b))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                         (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
                     then set_less_aux_Compl (lt_of_comp c)
                            (cproper_interval _A3) None
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) a)
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) b)
                     else true)
              else failwith "cless_set Complement2: infinite set"
                     (fun _ ->
                       cless_set (_A1, _A2, _A3, _A4) a (Complement b))))
    | a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) a b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then lexordp (fun x y -> lt_of_comp c y x)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       a)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       b)
              else failwith "cless_set: infinite set"
                     (fun _ -> cless_set (_A1, _A2, _A3, _A4) a b)))
and cless_eq_set (_A1, _A2, _A3, _A4)
  a b = match a, b with
    Complement (RBT_set rbt1), RBT_set rbt2 ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "cless_eq_set (Complement RBT_set) RBT_set: ccompare = None"
            (fun _ ->
              cless_eq_set (_A1, _A2, _A3, _A4) (Complement (RBT_set rbt1))
                (RBT_set rbt2))
        | Some c ->
          finite (_A1, _A2, _A3.ccompare_cproper_interval)
            (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
            compl_set_less_eq_aux_fusion (lt_of_comp c) (cproper_interval _A3)
              rbt_keys_generator rbt_keys_generator None
              (init _A3.ccompare_cproper_interval rbt1)
              (init _A3.ccompare_cproper_interval rbt2))
    | RBT_set rbt1, Complement (RBT_set rbt2) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith
              "cless_eq_set RBT_set (Complement RBT_set): ccompare = None"
              (fun _ ->
                cless_eq_set (_A1, _A2, _A3, _A4) (RBT_set rbt1)
                  (Complement (RBT_set rbt2)))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                  (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
              then set_less_eq_aux_Compl_fusion (lt_of_comp c)
                     (cproper_interval _A3) rbt_keys_generator
                     rbt_keys_generator None
                     (init _A3.ccompare_cproper_interval rbt1)
                     (init _A3.ccompare_cproper_interval rbt2)
              else true))
    | RBT_set rbta, RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set RBT_set RBT_set: ccompare = None"
              (fun _ ->
                cless_eq_set (_A1, _A2, _A3, _A4) (RBT_set rbta) (RBT_set rbt))
          | Some c ->
            lexord_eq_fusion (fun x y -> lt_of_comp c y x) rbt_keys_generator
              rbt_keys_generator (init _A3.ccompare_cproper_interval rbta)
              (init _A3.ccompare_cproper_interval rbt))
    | Complement a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement Complement: ccompare = None"
              (fun _ ->
                le_of_comp (the (ccompare_seta (_A1, _A2, _A3, _A4)))
                  (Complement a) (Complement b))
          | Some _ -> cless_eq_set (_A1, _A2, _A3, _A4) b a)
    | Complement a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement1: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) (Complement a) b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then finite (_A1, _A2, _A3.ccompare_cproper_interval)
                     (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
                     compl_set_less_eq_aux (lt_of_comp c) (cproper_interval _A3)
                       None
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         a)
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         b)
              else failwith "cless_eq_set Complement1: infinite set"
                     (fun _ ->
                       cless_eq_set (_A1, _A2, _A3, _A4) (Complement a) b)))
    | a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement2: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a (Complement b))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                         (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
                     then set_less_eq_aux_Compl (lt_of_comp c)
                            (cproper_interval _A3) None
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) a)
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) b)
                     else true)
              else failwith "cless_eq_set Complement2: infinite set"
                     (fun _ ->
                       cless_eq_set (_A1, _A2, _A3, _A4) a (Complement b))))
    | a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then lexordp_eq (fun x y -> lt_of_comp c y x)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       a)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       b)
              else failwith "cless_eq_set: infinite set"
                     (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a b)));;

let rec ccompare_set (_A1, _A2, _A3, _A4) =
  ({ccompare = ccompare_seta (_A1, _A2, _A3, _A4)} : 'a set ccompare);;

let rec equal_boola p pa = match p, pa with false, p -> not p
                      | true, p -> p
                      | p, false -> not p
                      | p, true -> p;;

let equal_bool = ({equal = equal_boola} : bool equal);;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec typerep_lista _A t = Typerep ("List.list", [typerep _A Type]);;

let rec countable_list _A = (() : ('a list) countable);;

let rec typerep_list _A = ({typerep = typerep_lista _A} : ('a list) typerep);;

let rec heap_list _A =
  ({countable_heap = (countable_list _A.countable_heap);
     typerep_heap = (typerep_list _A.typerep_heap)}
    : ('a list) heap);;

let rec equality_list
  eq_a x1 x2 = match eq_a, x1, x2 with eq_a, [], [] -> true
    | eq_a, [], y :: ya -> false
    | eq_a, x :: xa, [] -> false
    | eq_a, x :: xa, y :: ya -> eq_a x y && equality_list eq_a xa ya;;

let rec ceq_lista _A
  = (match ceq _A with None -> None | Some eq_a -> Some (equality_list eq_a));;

let rec ceq_list _A = ({ceq = ceq_lista _A} : ('a list) ceq);;

let set_impl_lista : (('a list), set_impla) phantom = Phantom Set_Choose;;

let set_impl_list = ({set_impl = set_impl_lista} : ('a list) set_impl);;

let finite_UNIV_lista : (('a list), bool) phantom = Phantom false;;

let card_UNIV_lista : (('a list), nat) phantom = Phantom zero_nata;;

let finite_UNIV_list =
  ({finite_UNIV = finite_UNIV_lista} : ('a list) finite_UNIV);;

let card_UNIV_list =
  ({finite_UNIV_card_UNIV = finite_UNIV_list; card_UNIV = card_UNIV_lista} :
    ('a list) card_UNIV);;

let cEnum_list :
  (('a list) list *
    ((('a list -> bool) -> bool) * (('a list -> bool) -> bool))) option
  = None;;

let cenum_list = ({cEnum = cEnum_list} : ('a list) cenum);;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, [], [] -> Eqa
    | comp_a, [], y :: ya -> Lt
    | comp_a, x :: xa, [] -> Gt
    | comp_a, x :: xa, y :: ya ->
        (match comp_a x y with Eqa -> comparator_list comp_a xa ya | Lt -> Lt
          | Gt -> Gt);;

let rec ccompare_lista _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_list comp_a));;

let rec ccompare_list _A =
  ({ccompare = ccompare_lista _A} : ('a list) ccompare);;

let mapping_impl_lista : (('a list), mapping_impla) phantom
  = Phantom Mapping_Choose;;

let mapping_impl_list =
  ({mapping_impl = mapping_impl_lista} : ('a list) mapping_impl);;

let rec cproper_interval_lista _A xso yso = failwith "undefined";;

let rec cproper_interval_list _A =
  ({ccompare_cproper_interval = (ccompare_list _A);
     cproper_interval = cproper_interval_lista _A}
    : ('a list) cproper_interval);;

let rec lcompare_double
  x y = (if FloatUtil.iszero x && FloatUtil.iszero y
          then FloatUtil.compare (FloatUtil.copysign 1.0 x)
                 (FloatUtil.copysign 1.0 y)
          else FloatUtil.compare x y);;

let rec equal_double x y = Z.equal (lcompare_double x y) Z.zero;;

type event_data = EInt of Z.t | EFloat of float | EString of string;;

let rec equal_event_dataa
  x0 x1 = match x0, x1 with EFloat x2, EString x3 -> false
    | EString x3, EFloat x2 -> false
    | EInt x1, EString x3 -> false
    | EString x3, EInt x1 -> false
    | EInt x1, EFloat x2 -> false
    | EFloat x2, EInt x1 -> false
    | EString x3, EString y3 -> Stdlib.(=) x3 y3
    | EFloat x2, EFloat y2 -> equal_double x2 y2
    | EInt x1, EInt y1 -> Z.equal x1 y1;;

type trm = Var of nat | Const of event_data | Plus of trm * trm |
  Minus of trm * trm | UMinus of trm | Mult of trm * trm | Div of trm * trm |
  Mod of trm * trm | F2i of trm | I2f of trm;;

let rec equal_trma
  x0 x1 = match x0, x1 with F2i x9, I2f x10 -> false
    | I2f x10, F2i x9 -> false
    | Mod (x81, x82), I2f x10 -> false
    | I2f x10, Mod (x81, x82) -> false
    | Mod (x81, x82), F2i x9 -> false
    | F2i x9, Mod (x81, x82) -> false
    | Div (x71, x72), I2f x10 -> false
    | I2f x10, Div (x71, x72) -> false
    | Div (x71, x72), F2i x9 -> false
    | F2i x9, Div (x71, x72) -> false
    | Div (x71, x72), Mod (x81, x82) -> false
    | Mod (x81, x82), Div (x71, x72) -> false
    | Mult (x61, x62), I2f x10 -> false
    | I2f x10, Mult (x61, x62) -> false
    | Mult (x61, x62), F2i x9 -> false
    | F2i x9, Mult (x61, x62) -> false
    | Mult (x61, x62), Mod (x81, x82) -> false
    | Mod (x81, x82), Mult (x61, x62) -> false
    | Mult (x61, x62), Div (x71, x72) -> false
    | Div (x71, x72), Mult (x61, x62) -> false
    | UMinus x5, I2f x10 -> false
    | I2f x10, UMinus x5 -> false
    | UMinus x5, F2i x9 -> false
    | F2i x9, UMinus x5 -> false
    | UMinus x5, Mod (x81, x82) -> false
    | Mod (x81, x82), UMinus x5 -> false
    | UMinus x5, Div (x71, x72) -> false
    | Div (x71, x72), UMinus x5 -> false
    | UMinus x5, Mult (x61, x62) -> false
    | Mult (x61, x62), UMinus x5 -> false
    | Minus (x41, x42), I2f x10 -> false
    | I2f x10, Minus (x41, x42) -> false
    | Minus (x41, x42), F2i x9 -> false
    | F2i x9, Minus (x41, x42) -> false
    | Minus (x41, x42), Mod (x81, x82) -> false
    | Mod (x81, x82), Minus (x41, x42) -> false
    | Minus (x41, x42), Div (x71, x72) -> false
    | Div (x71, x72), Minus (x41, x42) -> false
    | Minus (x41, x42), Mult (x61, x62) -> false
    | Mult (x61, x62), Minus (x41, x42) -> false
    | Minus (x41, x42), UMinus x5 -> false
    | UMinus x5, Minus (x41, x42) -> false
    | Plus (x31, x32), I2f x10 -> false
    | I2f x10, Plus (x31, x32) -> false
    | Plus (x31, x32), F2i x9 -> false
    | F2i x9, Plus (x31, x32) -> false
    | Plus (x31, x32), Mod (x81, x82) -> false
    | Mod (x81, x82), Plus (x31, x32) -> false
    | Plus (x31, x32), Div (x71, x72) -> false
    | Div (x71, x72), Plus (x31, x32) -> false
    | Plus (x31, x32), Mult (x61, x62) -> false
    | Mult (x61, x62), Plus (x31, x32) -> false
    | Plus (x31, x32), UMinus x5 -> false
    | UMinus x5, Plus (x31, x32) -> false
    | Plus (x31, x32), Minus (x41, x42) -> false
    | Minus (x41, x42), Plus (x31, x32) -> false
    | Const x2, I2f x10 -> false
    | I2f x10, Const x2 -> false
    | Const x2, F2i x9 -> false
    | F2i x9, Const x2 -> false
    | Const x2, Mod (x81, x82) -> false
    | Mod (x81, x82), Const x2 -> false
    | Const x2, Div (x71, x72) -> false
    | Div (x71, x72), Const x2 -> false
    | Const x2, Mult (x61, x62) -> false
    | Mult (x61, x62), Const x2 -> false
    | Const x2, UMinus x5 -> false
    | UMinus x5, Const x2 -> false
    | Const x2, Minus (x41, x42) -> false
    | Minus (x41, x42), Const x2 -> false
    | Const x2, Plus (x31, x32) -> false
    | Plus (x31, x32), Const x2 -> false
    | Var x1, I2f x10 -> false
    | I2f x10, Var x1 -> false
    | Var x1, F2i x9 -> false
    | F2i x9, Var x1 -> false
    | Var x1, Mod (x81, x82) -> false
    | Mod (x81, x82), Var x1 -> false
    | Var x1, Div (x71, x72) -> false
    | Div (x71, x72), Var x1 -> false
    | Var x1, Mult (x61, x62) -> false
    | Mult (x61, x62), Var x1 -> false
    | Var x1, UMinus x5 -> false
    | UMinus x5, Var x1 -> false
    | Var x1, Minus (x41, x42) -> false
    | Minus (x41, x42), Var x1 -> false
    | Var x1, Plus (x31, x32) -> false
    | Plus (x31, x32), Var x1 -> false
    | Var x1, Const x2 -> false
    | Const x2, Var x1 -> false
    | I2f x10, I2f y10 -> equal_trma x10 y10
    | F2i x9, F2i y9 -> equal_trma x9 y9
    | Mod (x81, x82), Mod (y81, y82) -> equal_trma x81 y81 && equal_trma x82 y82
    | Div (x71, x72), Div (y71, y72) -> equal_trma x71 y71 && equal_trma x72 y72
    | Mult (x61, x62), Mult (y61, y62) ->
        equal_trma x61 y61 && equal_trma x62 y62
    | UMinus x5, UMinus y5 -> equal_trma x5 y5
    | Minus (x41, x42), Minus (y41, y42) ->
        equal_trma x41 y41 && equal_trma x42 y42
    | Plus (x31, x32), Plus (y31, y32) ->
        equal_trma x31 y31 && equal_trma x32 y32
    | Const x2, Const y2 -> equal_event_dataa x2 y2
    | Var x1, Var y1 -> equal_nata x1 y1;;

let equal_trm = ({equal = equal_trma} : trm equal);;

let ceq_trma : (trm -> trm -> bool) option = Some equal_trma;;

let ceq_trm = ({ceq = ceq_trma} : trm ceq);;

let set_impl_trma : (trm, set_impla) phantom = Phantom Set_RBT;;

let set_impl_trm = ({set_impl = set_impl_trma} : trm set_impl);;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eqa else Gt));;

let rec comparator_double
  x y = (let c = lcompare_double x y in
          (if Z.equal c Z.zero then Eqa
            else (if Z.lt c Z.zero then Lt else Gt)));;

let rec comparator_event_data
  x0 x1 = match x0, x1 with
    EInt x, EInt y ->
      (fun x y -> if Obj.is_int (Obj.repr x) && Obj.is_int (Obj.repr y) then (let a = (Obj.magic x : int) and b = (Obj.magic y : int) in if a < b then Lt else if a = b then Eqa else Gt) else (let c = Z.compare x y in if c < 0 then Lt else if c = 0 then Eqa else Gt))
        x y
    | EInt x, EFloat e -> Lt
    | EInt x, EString t -> Lt
    | EFloat d, EInt y -> Gt
    | EFloat d, EFloat e -> comparator_double d e
    | EFloat d, EString t -> Lt
    | EString s, EInt y -> Gt
    | EString s, EFloat e -> Gt
    | EString s, EString t ->
        (if Stdlib.(<) s t then Lt else (if Stdlib.(=) s t then Eqa else Gt));;

let rec comparator_trm
  x0 x1 = match x0, x1 with
    Var x, Var y -> comparator_of (equal_nat, linorder_nat) x y
    | Var x, Const ya -> Lt
    | Var x, Plus (yb, yc) -> Lt
    | Var x, Minus (yd, ye) -> Lt
    | Var x, UMinus yf -> Lt
    | Var x, Mult (yg, yh) -> Lt
    | Var x, Div (yi, yj) -> Lt
    | Var x, Mod (yk, yl) -> Lt
    | Var x, F2i ym -> Lt
    | Var x, I2f yn -> Lt
    | Const x, Var y -> Gt
    | Const x, Const ya -> comparator_event_data x ya
    | Const x, Plus (yb, yc) -> Lt
    | Const x, Minus (yd, ye) -> Lt
    | Const x, UMinus yf -> Lt
    | Const x, Mult (yg, yh) -> Lt
    | Const x, Div (yi, yj) -> Lt
    | Const x, Mod (yk, yl) -> Lt
    | Const x, F2i ym -> Lt
    | Const x, I2f yn -> Lt
    | Plus (x, xa), Var y -> Gt
    | Plus (x, xa), Const ya -> Gt
    | Plus (x, xa), Plus (yb, yc) ->
        (match comparator_trm x yb with Eqa -> comparator_trm xa yc | Lt -> Lt
          | Gt -> Gt)
    | Plus (x, xa), Minus (yd, ye) -> Lt
    | Plus (x, xa), UMinus yf -> Lt
    | Plus (x, xa), Mult (yg, yh) -> Lt
    | Plus (x, xa), Div (yi, yj) -> Lt
    | Plus (x, xa), Mod (yk, yl) -> Lt
    | Plus (x, xa), F2i ym -> Lt
    | Plus (x, xa), I2f yn -> Lt
    | Minus (x, xa), Var y -> Gt
    | Minus (x, xa), Const ya -> Gt
    | Minus (x, xa), Plus (yb, yc) -> Gt
    | Minus (x, xa), Minus (yd, ye) ->
        (match comparator_trm x yd with Eqa -> comparator_trm xa ye | Lt -> Lt
          | Gt -> Gt)
    | Minus (x, xa), UMinus yf -> Lt
    | Minus (x, xa), Mult (yg, yh) -> Lt
    | Minus (x, xa), Div (yi, yj) -> Lt
    | Minus (x, xa), Mod (yk, yl) -> Lt
    | Minus (x, xa), F2i ym -> Lt
    | Minus (x, xa), I2f yn -> Lt
    | UMinus x, Var y -> Gt
    | UMinus x, Const ya -> Gt
    | UMinus x, Plus (yb, yc) -> Gt
    | UMinus x, Minus (yd, ye) -> Gt
    | UMinus x, UMinus yf -> comparator_trm x yf
    | UMinus x, Mult (yg, yh) -> Lt
    | UMinus x, Div (yi, yj) -> Lt
    | UMinus x, Mod (yk, yl) -> Lt
    | UMinus x, F2i ym -> Lt
    | UMinus x, I2f yn -> Lt
    | Mult (x, xa), Var y -> Gt
    | Mult (x, xa), Const ya -> Gt
    | Mult (x, xa), Plus (yb, yc) -> Gt
    | Mult (x, xa), Minus (yd, ye) -> Gt
    | Mult (x, xa), UMinus yf -> Gt
    | Mult (x, xa), Mult (yg, yh) ->
        (match comparator_trm x yg with Eqa -> comparator_trm xa yh | Lt -> Lt
          | Gt -> Gt)
    | Mult (x, xa), Div (yi, yj) -> Lt
    | Mult (x, xa), Mod (yk, yl) -> Lt
    | Mult (x, xa), F2i ym -> Lt
    | Mult (x, xa), I2f yn -> Lt
    | Div (x, xa), Var y -> Gt
    | Div (x, xa), Const ya -> Gt
    | Div (x, xa), Plus (yb, yc) -> Gt
    | Div (x, xa), Minus (yd, ye) -> Gt
    | Div (x, xa), UMinus yf -> Gt
    | Div (x, xa), Mult (yg, yh) -> Gt
    | Div (x, xa), Div (yi, yj) ->
        (match comparator_trm x yi with Eqa -> comparator_trm xa yj | Lt -> Lt
          | Gt -> Gt)
    | Div (x, xa), Mod (yk, yl) -> Lt
    | Div (x, xa), F2i ym -> Lt
    | Div (x, xa), I2f yn -> Lt
    | Mod (x, xa), Var y -> Gt
    | Mod (x, xa), Const ya -> Gt
    | Mod (x, xa), Plus (yb, yc) -> Gt
    | Mod (x, xa), Minus (yd, ye) -> Gt
    | Mod (x, xa), UMinus yf -> Gt
    | Mod (x, xa), Mult (yg, yh) -> Gt
    | Mod (x, xa), Div (yi, yj) -> Gt
    | Mod (x, xa), Mod (yk, yl) ->
        (match comparator_trm x yk with Eqa -> comparator_trm xa yl | Lt -> Lt
          | Gt -> Gt)
    | Mod (x, xa), F2i ym -> Lt
    | Mod (x, xa), I2f yn -> Lt
    | F2i x, Var y -> Gt
    | F2i x, Const ya -> Gt
    | F2i x, Plus (yb, yc) -> Gt
    | F2i x, Minus (yd, ye) -> Gt
    | F2i x, UMinus yf -> Gt
    | F2i x, Mult (yg, yh) -> Gt
    | F2i x, Div (yi, yj) -> Gt
    | F2i x, Mod (yk, yl) -> Gt
    | F2i x, F2i ym -> comparator_trm x ym
    | F2i x, I2f yn -> Lt
    | I2f x, Var y -> Gt
    | I2f x, Const ya -> Gt
    | I2f x, Plus (yb, yc) -> Gt
    | I2f x, Minus (yd, ye) -> Gt
    | I2f x, UMinus yf -> Gt
    | I2f x, Mult (yg, yh) -> Gt
    | I2f x, Div (yi, yj) -> Gt
    | I2f x, Mod (yk, yl) -> Gt
    | I2f x, F2i ym -> Gt
    | I2f x, I2f yn -> comparator_trm x yn;;

let ccompare_trma : (trm -> trm -> ordera) option = Some comparator_trm;;

let ccompare_trm = ({ccompare = ccompare_trma} : trm ccompare);;

let rec equal_option _A = ({equal = equal_optiona _A} : ('a option) equal);;

let rec equality_option
  eq_a x1 x2 = match eq_a, x1, x2 with eq_a, None, None -> true
    | eq_a, None, Some y -> false
    | eq_a, Some x, None -> false
    | eq_a, Some x, Some y -> eq_a x y;;

let rec ceq_optiona _A
  = (match ceq _A with None -> None
      | Some eq_a -> Some (equality_option eq_a));;

let rec ceq_option _A = ({ceq = ceq_optiona _A} : ('a option) ceq);;

let rec set_impl_optiona _A = Phantom (of_phantom (set_impl _A));;

let rec set_impl_option _A =
  ({set_impl = set_impl_optiona _A} : ('a option) set_impl);;

let rec comparator_option
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, None, None -> Eqa
    | comp_a, None, Some y -> Lt
    | comp_a, Some x, None -> Gt
    | comp_a, Some x, Some y -> comp_a x y;;

let rec ccompare_optiona _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_option comp_a));;

let rec ccompare_option _A =
  ({ccompare = ccompare_optiona _A} : ('a option) ccompare);;

type mregex = MSkip of nat | MTestPos of nat | MTestNeg of nat |
  MPlus of mregex * mregex | MTimes of mregex * mregex | MStar of mregex;;

let rec equal_mregexa
  x0 x1 = match x0, x1 with MTimes (x51, x52), MStar x6 -> false
    | MStar x6, MTimes (x51, x52) -> false
    | MPlus (x41, x42), MStar x6 -> false
    | MStar x6, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MTimes (x51, x52) -> false
    | MTimes (x51, x52), MPlus (x41, x42) -> false
    | MTestNeg x3, MStar x6 -> false
    | MStar x6, MTestNeg x3 -> false
    | MTestNeg x3, MTimes (x51, x52) -> false
    | MTimes (x51, x52), MTestNeg x3 -> false
    | MTestNeg x3, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MTestNeg x3 -> false
    | MTestPos x2, MStar x6 -> false
    | MStar x6, MTestPos x2 -> false
    | MTestPos x2, MTimes (x51, x52) -> false
    | MTimes (x51, x52), MTestPos x2 -> false
    | MTestPos x2, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MTestPos x2 -> false
    | MTestPos x2, MTestNeg x3 -> false
    | MTestNeg x3, MTestPos x2 -> false
    | MSkip x1, MStar x6 -> false
    | MStar x6, MSkip x1 -> false
    | MSkip x1, MTimes (x51, x52) -> false
    | MTimes (x51, x52), MSkip x1 -> false
    | MSkip x1, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MSkip x1 -> false
    | MSkip x1, MTestNeg x3 -> false
    | MTestNeg x3, MSkip x1 -> false
    | MSkip x1, MTestPos x2 -> false
    | MTestPos x2, MSkip x1 -> false
    | MStar x6, MStar y6 -> equal_mregexa x6 y6
    | MTimes (x51, x52), MTimes (y51, y52) ->
        equal_mregexa x51 y51 && equal_mregexa x52 y52
    | MPlus (x41, x42), MPlus (y41, y42) ->
        equal_mregexa x41 y41 && equal_mregexa x42 y42
    | MTestNeg x3, MTestNeg y3 -> equal_nata x3 y3
    | MTestPos x2, MTestPos y2 -> equal_nata x2 y2
    | MSkip x1, MSkip y1 -> equal_nata x1 y1;;

let equal_mregex = ({equal = equal_mregexa} : mregex equal);;

let rec comparator_mregex
  x0 x1 = match x0, x1 with
    MSkip x, MSkip y -> comparator_of (equal_nat, linorder_nat) x y
    | MSkip x, MTestPos ya -> Lt
    | MSkip x, MTestNeg yb -> Lt
    | MSkip x, MPlus (yc, yd) -> Lt
    | MSkip x, MTimes (ye, yf) -> Lt
    | MSkip x, MStar yg -> Lt
    | MTestPos x, MSkip y -> Gt
    | MTestPos x, MTestPos ya -> comparator_of (equal_nat, linorder_nat) x ya
    | MTestPos x, MTestNeg yb -> Lt
    | MTestPos x, MPlus (yc, yd) -> Lt
    | MTestPos x, MTimes (ye, yf) -> Lt
    | MTestPos x, MStar yg -> Lt
    | MTestNeg x, MSkip y -> Gt
    | MTestNeg x, MTestPos ya -> Gt
    | MTestNeg x, MTestNeg yb -> comparator_of (equal_nat, linorder_nat) x yb
    | MTestNeg x, MPlus (yc, yd) -> Lt
    | MTestNeg x, MTimes (ye, yf) -> Lt
    | MTestNeg x, MStar yg -> Lt
    | MPlus (x, xa), MSkip y -> Gt
    | MPlus (x, xa), MTestPos ya -> Gt
    | MPlus (x, xa), MTestNeg yb -> Gt
    | MPlus (x, xa), MPlus (yc, yd) ->
        (match comparator_mregex x yc with Eqa -> comparator_mregex xa yd
          | Lt -> Lt | Gt -> Gt)
    | MPlus (x, xa), MTimes (ye, yf) -> Lt
    | MPlus (x, xa), MStar yg -> Lt
    | MTimes (x, xa), MSkip y -> Gt
    | MTimes (x, xa), MTestPos ya -> Gt
    | MTimes (x, xa), MTestNeg yb -> Gt
    | MTimes (x, xa), MPlus (yc, yd) -> Gt
    | MTimes (x, xa), MTimes (ye, yf) ->
        (match comparator_mregex x ye with Eqa -> comparator_mregex xa yf
          | Lt -> Lt | Gt -> Gt)
    | MTimes (x, xa), MStar yg -> Lt
    | MStar x, MSkip y -> Gt
    | MStar x, MTestPos ya -> Gt
    | MStar x, MTestNeg yb -> Gt
    | MStar x, MPlus (yc, yd) -> Gt
    | MStar x, MTimes (ye, yf) -> Gt
    | MStar x, MStar yg -> comparator_mregex x yg;;

let rec less_eq_mregex x = le_of_comp comparator_mregex x;;

let rec less_mregex x = lt_of_comp comparator_mregex x;;

let ord_mregex = ({less_eq = less_eq_mregex; less = less_mregex} : mregex ord);;

let preorder_mregex = ({ord_preorder = ord_mregex} : mregex preorder);;

let order_mregex = ({preorder_order = preorder_mregex} : mregex order);;

let ceq_mregexa : (mregex -> mregex -> bool) option = Some equal_mregexa;;

let ceq_mregex = ({ceq = ceq_mregexa} : mregex ceq);;

let set_impl_mregexa : (mregex, set_impla) phantom = Phantom Set_RBT;;

let set_impl_mregex = ({set_impl = set_impl_mregexa} : mregex set_impl);;

let linorder_mregex = ({order_linorder = order_mregex} : mregex linorder);;

let cEnum_mregex :
  (mregex list *
    (((mregex -> bool) -> bool) * ((mregex -> bool) -> bool))) option
  = None;;

let cenum_mregex = ({cEnum = cEnum_mregex} : mregex cenum);;

let ccompare_mregexa : (mregex -> mregex -> ordera) option
  = Some comparator_mregex;;

let ccompare_mregex = ({ccompare = ccompare_mregexa} : mregex ccompare);;

type enat = Enat of nat | Infinity_enat;;

let rec equal_enat x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                     | Infinity_enat, Enat nat -> false
                     | Enat nata, Enat nat -> equal_nata nata nat
                     | Infinity_enat, Infinity_enat -> true;;

let ceq_enata : (enat -> enat -> bool) option = Some equal_enat;;

let ceq_enat = ({ceq = ceq_enata} : enat ceq);;

let set_impl_enata : (enat, set_impla) phantom = Phantom Set_RBT;;

let set_impl_enat = ({set_impl = set_impl_enata} : enat set_impl);;

let finite_UNIV_enata : (enat, bool) phantom = Phantom false;;

let finite_UNIV_enat = ({finite_UNIV = finite_UNIV_enata} : enat finite_UNIV);;

let rec less_enat x0 q = match x0, q with Enat m, Enat n -> less_nat m n
                    | Enat m, Infinity_enat -> true
                    | Infinity_enat, q -> false;;

let ccompare_enata : (enat -> enat -> ordera) option
  = Some (fun x y ->
           (if equal_enat x y then Eqa
             else (if less_enat x y then Lt else Gt)));;

let ccompare_enat = ({ccompare = ccompare_enata} : enat ccompare);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec equality_prod eq_a eq_b (x, xa) (y, ya) = eq_a x y && eq_b xa ya;;

let rec ceq_proda _A _B
  = (match ceq _A with None -> None
      | Some eq_a ->
        (match ceq _B with None -> None
          | Some eq_b -> Some (equality_prod eq_a eq_b)));;

let rec ceq_prod _A _B = ({ceq = ceq_proda _A _B} : ('a * 'b) ceq);;

let rec set_impl_choose2
  x y = match x, y with Set_Monada, Set_Monada -> Set_Monada
    | Set_RBT, Set_RBT -> Set_RBT
    | Set_DList, Set_DList -> Set_DList
    | Set_Collect, Set_Collect -> Set_Collect
    | x, y -> Set_Choose;;

let rec set_impl_proda _A _B
  = Phantom
      (set_impl_choose2 (of_phantom (set_impl _A)) (of_phantom (set_impl _B)));;

let rec set_impl_prod _A _B =
  ({set_impl = set_impl_proda _A _B} : ('a * 'b) set_impl);;

let rec finite_UNIV_proda _A _B
  = Phantom (of_phantom (finite_UNIV _A) && of_phantom (finite_UNIV _B));;

let rec finite_UNIV_prod _A _B =
  ({finite_UNIV = finite_UNIV_proda _A _B} : ('a * 'b) finite_UNIV);;

let rec comparator_prod
  comp_a comp_b (x, xa) (y, ya) =
    (match comp_a x y with Eqa -> comp_b xa ya | Lt -> Lt | Gt -> Gt);;

let rec ccompare_proda _A _B
  = (match ccompare _A with None -> None
      | Some comp_a ->
        (match ccompare _B with None -> None
          | Some comp_b -> Some (comparator_prod comp_a comp_b)));;

let rec ccompare_prod _A _B =
  ({ccompare = ccompare_proda _A _B} : ('a * 'b) ccompare);;

type rec_safety = Unused | PastRec | NonFutuRec | AnyRec;;

let rec equal_rec_safety x0 x1 = match x0, x1 with NonFutuRec, AnyRec -> false
                           | AnyRec, NonFutuRec -> false
                           | PastRec, AnyRec -> false
                           | AnyRec, PastRec -> false
                           | PastRec, NonFutuRec -> false
                           | NonFutuRec, PastRec -> false
                           | Unused, AnyRec -> false
                           | AnyRec, Unused -> false
                           | Unused, NonFutuRec -> false
                           | NonFutuRec, Unused -> false
                           | Unused, PastRec -> false
                           | PastRec, Unused -> false
                           | AnyRec, AnyRec -> true
                           | NonFutuRec, NonFutuRec -> true
                           | PastRec, PastRec -> true
                           | Unused, Unused -> true;;

let ceq_rec_safetya : (rec_safety -> rec_safety -> bool) option
  = Some equal_rec_safety;;

let ceq_rec_safety = ({ceq = ceq_rec_safetya} : rec_safety ceq);;

let set_impl_rec_safetya : (rec_safety, set_impla) phantom = Phantom Set_DList;;

let set_impl_rec_safety =
  ({set_impl = set_impl_rec_safetya} : rec_safety set_impl);;

let rec comparator_rec_safety x0 x1 = match x0, x1 with Unused, Unused -> Eqa
                                | Unused, PastRec -> Lt
                                | Unused, NonFutuRec -> Lt
                                | Unused, AnyRec -> Lt
                                | PastRec, Unused -> Gt
                                | PastRec, PastRec -> Eqa
                                | PastRec, NonFutuRec -> Lt
                                | PastRec, AnyRec -> Lt
                                | NonFutuRec, Unused -> Gt
                                | NonFutuRec, PastRec -> Gt
                                | NonFutuRec, NonFutuRec -> Eqa
                                | NonFutuRec, AnyRec -> Lt
                                | AnyRec, Unused -> Gt
                                | AnyRec, PastRec -> Gt
                                | AnyRec, NonFutuRec -> Gt
                                | AnyRec, AnyRec -> Eqa;;

let ccompare_rec_safetya : (rec_safety -> rec_safety -> ordera) option
  = Some comparator_rec_safety;;

let ccompare_rec_safety =
  ({ccompare = ccompare_rec_safetya} : rec_safety ccompare);;

let equal_string8 = ({equal = Stdlib.(=)} : string equal);;

let ord_string8 = ({less_eq = Stdlib.(<=); less = Stdlib.(<)} : string ord);;

let preorder_string8 = ({ord_preorder = ord_string8} : string preorder);;

let order_string8 = ({preorder_order = preorder_string8} : string order);;

let linorder_string8 = ({order_linorder = order_string8} : string linorder);;

let rec compare_string8
  x y = (if Stdlib.(<) x y then Lt else (if Stdlib.(=) x y then Eqa else Gt));;

let ccompare_string8a : (string -> string -> ordera) option
  = Some compare_string8;;

let ccompare_string8 = ({ccompare = ccompare_string8a} : string ccompare);;

let mapping_impl_string8a : (string, mapping_impla) phantom
  = Phantom Mapping_RBT;;

let mapping_impl_string8 =
  ({mapping_impl = mapping_impl_string8a} : string mapping_impl);;

let equal_integer = ({equal = Z.equal} : Z.t equal);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let preorder_integer = ({ord_preorder = ord_integer} : Z.t preorder);;

let order_integer = ({preorder_order = preorder_integer} : Z.t order);;

let linorder_integer = ({order_linorder = order_integer} : Z.t linorder);;

let equal_event_data = ({equal = equal_event_dataa} : event_data equal);;

let rec typerep_event_dataa t = Typerep ("Event_Data.event_data", []);;

let countable_event_data = (() : event_data countable);;

let typerep_event_data =
  ({typerep = typerep_event_dataa} : event_data typerep);;

let heap_event_data =
  ({countable_heap = countable_event_data; typerep_heap = typerep_event_data} :
    event_data heap);;

let rec less_eq_event_data
  x0 x1 = match x0, x1 with EInt x, EInt y -> Z.leq x y
    | EFloat x, EFloat y -> Stdlib.(<=) x y
    | EString x, EString y -> Stdlib.(<=) x y
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, EInt va -> failwith "undefined"
    | EString v, EFloat va -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | EInt va, EString v -> failwith "undefined";;

let rec less_event_data
  x y = less_eq_event_data x y && not (less_eq_event_data y x);;

let ord_event_data =
  ({less_eq = less_eq_event_data; less = less_event_data} : event_data ord);;

let ceq_event_dataa : (event_data -> event_data -> bool) option
  = Some equal_event_dataa;;

let ceq_event_data = ({ceq = ceq_event_dataa} : event_data ceq);;

let set_impl_event_dataa : (event_data, set_impla) phantom = Phantom Set_RBT;;

let set_impl_event_data =
  ({set_impl = set_impl_event_dataa} : event_data set_impl);;

let cEnum_event_data :
  (event_data list *
    (((event_data -> bool) -> bool) * ((event_data -> bool) -> bool))) option
  = None;;

let cenum_event_data = ({cEnum = cEnum_event_data} : event_data cenum);;

let finite_UNIV_event_dataa : (event_data, bool) phantom = Phantom false;;

let finite_UNIV_event_data =
  ({finite_UNIV = finite_UNIV_event_dataa} : event_data finite_UNIV);;

let ccompare_event_dataa : (event_data -> event_data -> ordera) option
  = Some comparator_event_data;;

let ccompare_event_data =
  ({ccompare = ccompare_event_dataa} : event_data ccompare);;

type 'a dq = Dq of 'a list * 'a list * nat * nat;;

type ('b, 'a) alist = Alist of ('b * 'a) list;;

type ('a, 'b) mapping = Assoc_List_Mapping of ('a, 'b) alist |
  RBT_Mapping of ('a, 'b) mapping_rbt | Mapping of ('a -> 'b option);;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

type 'a queue = Abs_queue of ('a list * 'a list);;

type uduaux_x =
  UDUX_gen of
    (nat *
      (nat queue *
        (((event_data list) set * (nat, nat) sum) queue *
          (nat *
            (bool list *
              (bool list *
                ((event_data list) set *
                  (((event_data list), nat) mapping *
                    (((event_data list), (nat, nat) sum) mapping dq *
                      (nat dq * (event_data list) set list))))))))))
  | UDUX_win of
      (nat queue *
        ((nat * ((event_data list) set * bool)) queue *
          ((nat * ((event_data list) set * bool)) queue *
            (nat *
              (bool *
                ((((event_data list), nat) mapping * (event_data list) set) *
                  (event_data list) set list))))));;

type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree;;

type 'a wf_wbt = Abs_wf_wbt of ('a * nat) tree;;

type 'a treelist = Collapse of 'a wf_wbt;;

type list_aux = LInt of Z.t treelist | LString of string treelist;;

type typea = IntT | StringT;;

type aggaux = CntAux of (((event_data option) list), nat) mapping |
  SumAux of (((event_data option) list), (nat * Z.t)) mapping |
  RankAux of ((((event_data option) list), list_aux) mapping * typea);;

type agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med;;

type ty = TInt | TFloat | TString;;

type udsaux_x =
  UDSX_gen of
    (nat *
      (nat *
        (bool list *
          ((nat * (event_data list) set) queue *
            ((nat * (event_data list) set) queue *
              ((event_data list) set *
                (((event_data list), (event_data list) set) mapping *
                  (((event_data list), nat) mapping *
                    (((event_data list), (event_data list) set) mapping *
                      ((event_data list), nat) mapping)))))))))
  | UDSX_win of
      (nat *
        ((nat * (event_data list) set) queue *
          ((nat * (event_data list) set) queue *
            (((event_data list), nat) mapping * (event_data list) set))))
  | UDSX_wagg of
      (bool * ((agg_type * ty) * (trm * (nat * nat)))) *
        ((nat *
           ((nat * (event_data list) set) queue *
             ((nat * (event_data list) set) queue *
               (((event_data list), nat) mapping * (event_data list) set)))) *
          aggaux option);;

type 'a aggargs_ext =
  Aggargs_ext of
    nat set * nat * bool * nat * (agg_type * ty) * ty list * trm * 'a;;

type i = Abs_I of ((nat -> bool) * ((nat -> bool) * bool));;

type 'a args_ext =
  Args_ext of
    i * nat * nat set * nat set * bool * unit aggargs_ext option * 'a;;

type 'a mbuf_t = MBuf2_t of 'a queue;;

type mconstraint = MEq | MLess | MLessEq;;

type mrg = MLft | MRgt | MBth;;

type djoin_plan = DJEq | DJEmp | DJSub of bool list | DJSup of bool list |
  DJGen of mrg list * bool list * bool list;;

type mtrm = MVar of nat | MConst of event_data;;

type udformula = UDFail | UDRel of (event_data list) set |
  UDPredS of string * nat | UDPredM of string * nat * trm list * nat list |
  UDAndRel of udformula * (trm * (bool * (mconstraint * trm))) |
  UDNeg of udformula | UDExists of udformula * bool |
  UDAgg of bool * (agg_type * ty) * trm * nat * nat * udformula |
  UDOr of
    udformula * udformula *
      ((event_data list) set mbuf_t * (event_data list) set mbuf_t)
  | UDAnd of
      djoin_plan * udformula * bool * udformula *
        ((event_data list) set mbuf_t * (event_data list) set mbuf_t)
  | UDPrev of i * udformula * bool * (event_data list) set mbuf_t * nat mbuf_t |
  UDNext of i * udformula * bool * nat mbuf_t |
  UDAnds of
    djoin_plan list * djoin_plan list * udformula list *
      (event_data list) set mbuf_t list
  | UDSince of
      unit args_ext * udformula * udformula *
        ((event_data list) set mbuf_t *
          ((event_data list) set mbuf_t * (nat mbuf_t * bool))) *
        udsaux_x
  | UDUntil of
      unit args_ext * bool list * udformula * udformula *
        ((event_data list) set mbuf_t * (event_data list) set mbuf_t) *
        nat mbuf_t * nat * uduaux_x
  | UDAndAssign of nat * trm * udformula | UDTP of mtrm * nat | UDTS of mtrm |
  UDLet of string * nat * udformula * udformula |
  UDFrz of
    string * nat * udformula * udformula * nat * nat * nat *
      (event_data list) set list
  | UDLetPast of
      string * nat * udformula * udformula * nat * (event_data list) set option
  | UDTrigger of
      unit args_ext * (nat option) list * udformula * udformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t) *
        nat mbuf_t *
        (nat *
          (nat *
            (nat *
              (nat *
                (bool list *
                  (bool list *
                    ((nat *
                       (((event_data option) list) set *
                         ((event_data option) list) set))
                       queue *
                      ((nat * ((event_data option) list) set) queue *
                        ((((event_data option) list), nat) mapping *
                          (((event_data option) list) set *
                            ((((event_data option) list), nat) mapping *
                              (((event_data option) list) set *
                                ((event_data option) list) set))))))))))));;

let rec size_list
  x xa1 = match x, xa1 with x, [] -> zero_nata
    | x, x21 :: x22 ->
        plus_nata (plus_nata (x x21) (size_list x x22)) (suc zero_nata);;

let rec size_udformulaa
  = function UDFail -> zero_nata
    | UDRel x2 -> zero_nata
    | UDPredS (x31, x32) -> zero_nata
    | UDPredM (x41, x42, x43, x44) -> zero_nata
    | UDAndRel (x51, x52) -> plus_nata (size_udformulaa x51) (suc zero_nata)
    | UDNeg x6 -> plus_nata (size_udformulaa x6) (suc zero_nata)
    | UDExists (x71, x72) -> plus_nata (size_udformulaa x71) (suc zero_nata)
    | UDAgg (x81, x82, x83, x84, x85, x86) ->
        plus_nata (size_udformulaa x86) (suc zero_nata)
    | UDOr (x91, x92, x93) ->
        plus_nata (plus_nata (size_udformulaa x91) (size_udformulaa x92))
          (suc zero_nata)
    | UDAnd (x101, x102, x103, x104, x105) ->
        plus_nata (plus_nata (size_udformulaa x102) (size_udformulaa x104))
          (suc zero_nata)
    | UDPrev (x111, x112, x113, x114, x115) ->
        plus_nata (size_udformulaa x112) (suc zero_nata)
    | UDNext (x121, x122, x123, x124) ->
        plus_nata (size_udformulaa x122) (suc zero_nata)
    | UDAnds (x131, x132, x133, x134) ->
        plus_nata (size_list size_udformulaa x133) (suc zero_nata)
    | UDSince (x141, x142, x143, x144, x145) ->
        plus_nata (plus_nata (size_udformulaa x142) (size_udformulaa x143))
          (suc zero_nata)
    | UDUntil (x151, x152, x153, x154, x155, x156, x157, x158) ->
        plus_nata (plus_nata (size_udformulaa x153) (size_udformulaa x154))
          (suc zero_nata)
    | UDAndAssign (x161, x162, x163) ->
        plus_nata (size_udformulaa x163) (suc zero_nata)
    | UDTP (x171, x172) -> zero_nata
    | UDTS x18 -> zero_nata
    | UDLet (x191, x192, x193, x194) ->
        plus_nata (plus_nata (size_udformulaa x193) (size_udformulaa x194))
          (suc zero_nata)
    | UDFrz (x201, x202, x203, x204, x205, x206, x207, x208) ->
        plus_nata (plus_nata (size_udformulaa x203) (size_udformulaa x204))
          (suc zero_nata)
    | UDLetPast (x211, x212, x213, x214, x215, x216) ->
        plus_nata (plus_nata (size_udformulaa x213) (size_udformulaa x214))
          (suc zero_nata)
    | UDTrigger (x221, x222, x223, x224, x225, x226, x227) ->
        plus_nata (plus_nata (size_udformulaa x223) (size_udformulaa x224))
          (suc zero_nata);;

type 'a size = {size : 'a -> nat};;
let size _A = _A.size;;

let size_udformula = ({size = size_udformulaa} : udformula size);;

type int = Int_of_integer of Z.t;;

type cmp_val = LT | EQ | GT;;

type 'a regex = Skip of nat | Test of 'a | Plusa of 'a regex * 'a regex |
  Times of 'a regex * 'a regex | Star of 'a regex;;

type safety = Strict | Lax;;

type tysym = TAny of nat | TNum of nat | TCst of ty;;

type modality = Past | Futu;;

type 'a formula = Pred of string * trm list |
  Let of string * 'a formula * 'a formula |
  Frz of string * 'a formula * 'a formula |
  LetPast of string * 'a formula * 'a formula | Eq of trm * trm |
  Less of trm * trm | LessEq of trm * trm | Neg of 'a formula |
  Or of 'a formula * 'a formula | And of 'a formula * 'a formula |
  Ands of 'a formula list | Exists of 'a * 'a formula |
  Agg of nat * (agg_type * 'a) * 'a list * trm * 'a formula |
  Prev of i * 'a formula | Next of i * 'a formula |
  Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula |
  Trigger of 'a formula * i * 'a formula |
  Release of 'a formula * i * 'a formula | MatchF of i * 'a formula regex |
  MatchP of i * 'a formula regex | TP of trm | TS of trm;;

type 'a wf_idx =
  Abs_wf_idx of
    (nat *
      (nat set *
        (nat set * ((('a option) list), (('a option) list) set) mapping)));;

type 'a wf_set = Abs_wf_set of (nat * (nat set * (('a option) list) set));;

type pred_mode = Copy | Simple | Match;;

type ('a, 'b, 'c) meformula = MRel of ((event_data option) list) set |
  MPred of string * trm list * pred_mode |
  MLet of string * nat * ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula |
  MFrz of
    string * nat * ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula * nat * nat *
      nat * ((event_data option) list) set list
  | MLetPast of
      string * nat * ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula * nat *
        ((event_data option) list) set option
  | MAnd of
      nat set * ('a, 'b, 'c) meformula * bool * nat set *
        ('a, 'b, 'c) meformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t)
  | MAndAssign of ('a, 'b, 'c) meformula * (nat * trm) |
  MAndRel of ('a, 'b, 'c) meformula * (trm * (bool * (mconstraint * trm))) |
  MAndTrigger of
    nat set * ('a, 'b, 'c) meformula *
      (((event_data option) list) set mbuf_t *
        (nat set * ((event_data option) list) set) mbuf_t) *
      unit args_ext * ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula *
      (((event_data option) list) set mbuf_t *
        ((event_data option) list) set mbuf_t) *
      nat mbuf_t * 'c
  | MAnds of
      nat set list * nat set list * ('a, 'b, 'c) meformula list *
        ((event_data option) list) set mbuf_t list
  | MOr of
      ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t)
  | MNeg of ('a, 'b, 'c) meformula | MExists of ('a, 'b, 'c) meformula |
  MAgg of unit aggargs_ext * ('a, 'b, 'c) meformula |
  MPrev of
    i * ('a, 'b, 'c) meformula * bool * ((event_data option) list) set mbuf_t *
      nat mbuf_t
  | MNext of i * ('a, 'b, 'c) meformula * bool * nat mbuf_t |
  MSince of
    unit args_ext * ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula *
      (((event_data option) list) set mbuf_t *
        (((event_data option) list) set mbuf_t * (nat mbuf_t * bool))) *
      'a
  | MUntil of
      unit args_ext * ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t) *
        nat mbuf_t * nat * 'b
  | MTrigger of
      unit args_ext * ('a, 'b, 'c) meformula * ('a, 'b, 'c) meformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t) *
        nat mbuf_t * 'c
  | MMatchP of
      i * mregex * mregex list * ('a, 'b, 'c) meformula list *
        ((event_data option) list) set mbuf_t list * nat mbuf_t *
        (nat * (mregex, ((event_data option) list) set) mapping) list
  | MMatchF of
      i * mregex * mregex list * ('a, 'b, 'c) meformula list *
        ((event_data option) list) set mbuf_t list * nat mbuf_t * nat *
        (nat *
          (((event_data option) list) set list *
            ((event_data option) list) set)) list
  | MTP of mtrm * nat | MTS of mtrm;;

type ('a, 'b, 'c) mformula = Rep_meformula of ('a, 'b, 'c) meformula;;

type 'a daggargs_ext =
  Daggargs_ext of bool * (agg_type * ty) * trm * nat * nat * 'a;;

type daggaux = DCntAux of ((event_data list), nat) mapping |
  DSumAux of ((event_data list), (nat * Z.t)) mapping |
  DRankAux of (((event_data list), list_aux) mapping * typea);;

type msaux_d =
  MSD_imp of
    ((nat *
       (nat *
         (bool list *
           (bool list *
             ((nat * (event_data list) set) queue *
               ((nat * (event_data list) set) queue *
                 (event_data list) set)))))) *
      ((Z.t * (Z.t * ((Z.t * (event_data list * nat)) list) array)) *
        (Z.t * (Z.t * ((Z.t * (event_data list * nat)) list) array))))
  | MSD_dns of
      (nat *
        (nat *
          (bool list *
            ((nat * (event_data list) set) queue *
              ((nat * (event_data list) set) queue *
                ((event_data list) set *
                  (((event_data list), (event_data list) set) mapping *
                    (((event_data list), nat) mapping *
                      (((event_data list), (event_data list) set) mapping *
                        ((event_data list), nat) mapping)))))))))
  | MSD_evt of
      (nat *
        ((nat * (event_data list) set) queue *
          ((nat * (event_data list) set) queue *
            (((event_data list), nat) mapping * (event_data list) set))))
  | MSD_agg of
      unit daggargs_ext *
        ((nat *
           (nat *
             (bool list *
               ((nat * (event_data list) set) queue *
                 ((nat * (event_data list) set) queue *
                   ((event_data list) set *
                     (((event_data list), (event_data list) set) mapping *
                       (((event_data list), nat) mapping *
                         (((event_data list), (event_data list) set) mapping *
                           ((event_data list), nat) mapping))))))))) *
          daggaux option);;

type muaux_d =
  MUD_dns of
    (nat *
      (nat queue *
        (((event_data list) set * (nat, nat) sum) queue *
          (nat *
            (bool list *
              (bool list *
                ((event_data list) set *
                  (((event_data list), nat) mapping *
                    (((event_data list), (nat, nat) sum) mapping dq *
                      (nat dq * (event_data list) set list))))))))))
  | MUD_evt of
      (nat queue *
        ((nat * ((event_data list) set * bool)) queue *
          ((nat * ((event_data list) set * bool)) queue *
            (nat *
              (bool *
                (((event_data list), nat) mapping *
                  ((event_data list) set * (event_data list) set list)))))))
  | MUD_agg of
      unit daggargs_ext *
        ((nat *
           (nat queue *
             (((event_data list) set * (nat, nat) sum) queue *
               (nat *
                 (bool list *
                   (bool list *
                     ((event_data list) set *
                       (((event_data list), nat) mapping *
                         (((event_data list), (nat, nat) sum) mapping dq *
                           (nat dq * (event_data list) set list)))))))))) *
          daggaux option);;

type 'a wf_table = Wf_table_of_wf_set of 'a wf_set |
  Wf_table_of_idx of 'a wf_idx |
  Wf_table_of_set of nat * nat set * (('a option) list) set |
  Wf_table_of_keys of nat * nat set * ((('a option) list), nat) mapping;;

type dformula = DFail | DRel of (event_data list) set | DPredS of string * nat |
  DPredM of string * nat * trm list * nat list |
  DAnd of
    djoin_plan * dformula * bool * dformula *
      ((event_data list) set mbuf_t * (event_data list) set mbuf_t)
  | DAnds of
      djoin_plan list * djoin_plan list * dformula list *
        (event_data list) set mbuf_t list
  | DAndRel of dformula * (trm * (bool * (mconstraint * trm))) |
  DOr of
    dformula * dformula *
      ((event_data list) set mbuf_t * (event_data list) set mbuf_t)
  | DNeg of dformula | DExists of dformula * bool |
  DAgg of bool * (agg_type * ty) * trm * nat * nat * dformula |
  DPrev of i * dformula * bool * (event_data list) set mbuf_t * nat mbuf_t |
  DNext of i * dformula * bool * nat mbuf_t |
  DSince of
    unit args_ext * dformula * dformula *
      ((event_data list) set mbuf_t *
        ((event_data list) set mbuf_t * (nat mbuf_t * bool))) *
      msaux_d
  | DUntil of
      unit args_ext * bool list * dformula * dformula *
        ((event_data list) set mbuf_t * (event_data list) set mbuf_t) *
        nat mbuf_t * nat * muaux_d
  | DAndAssign of nat * trm * dformula | DTP of mtrm * nat | DTS of mtrm |
  DLet of string * nat * dformula * dformula |
  DFrz of
    string * nat * dformula * dformula * nat * nat * nat *
      (event_data list) set list
  | DLetPast of
      string * nat * dformula * dformula * nat * (event_data list) set option
  | DTrigger of
      unit args_ext * dformula * dformula *
        ((event_data list) set mbuf_t * (event_data list) set mbuf_t) *
        nat mbuf_t *
        (nat *
          (nat *
            (nat *
              (nat *
                (bool list *
                  ((nat * ((event_data list) set * (event_data list) set))
                     queue *
                    ((nat * (event_data list) set) queue *
                      (((event_data list), nat) mapping *
                        ((event_data list) set *
                          (((event_data list), nat) mapping *
                            ((event_data list) set *
                              (event_data list) set)))))))))))
  | DAndTrigger of
      djoin_plan * dformula *
        (((event_data list) set option) mbuf_t *
          ((event_data list) set option) mbuf_t) *
        unit args_ext * dformula * dformula *
        ((event_data list) set mbuf_t * (event_data list) set mbuf_t) *
        nat mbuf_t *
        (nat *
          (nat *
            (nat *
              (nat *
                (bool list *
                  ((nat * ((event_data list) set * (event_data list) set))
                     queue *
                    ((nat * (event_data list) set) queue *
                      (((event_data list), nat) mapping *
                        ((event_data list) set *
                          (((event_data list), nat) mapping *
                            ((event_data list) set *
                              (event_data list) set)))))))))))
  | DMatchP of
      i * mregex * mregex list * (bool list) list * dformula list *
        (event_data list) set mbuf_t list * nat mbuf_t *
        (nat * (mregex, (event_data list) set) mapping) list
  | DMatchF of
      i * mregex * mregex list * (bool list) list * dformula list *
        (event_data list) set mbuf_t list * nat mbuf_t * nat *
        (nat * ((event_data list) set list * (event_data list) set)) list;;

type 'a boxed = Box of 'a;;

type ('b, 'a) comp_fun_idem = Abs_comp_fun_idem of ('b -> 'a -> 'a);;

type 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);;

type ('a, 'b, 'c, 'd) mstate_ext =
  Mestate of nat * nat * ('a, 'b, 'c) mformula * nat * nat queue * 'd;;

type ('b, 'a) comp_fun_commute = Abs_comp_fun_commute of ('b -> 'a -> 'a);;

type muaux_dq =
  MU_agg of
    ((nat *
       (nat queue *
         ((((event_data option) list) set * (nat, nat) sum) queue *
           (nat *
             (bool list *
               (bool list *
                 (((event_data option) list) set *
                   ((((event_data option) list), nat) mapping *
                     ((nat, (((event_data option) list), (nat, nat) sum)
                              mapping)
                        mapping *
                       ((nat, nat) mapping *
                         ((event_data option) list) set list)))))))))) *
      aggaux option)
  | MU_dq of
      (nat *
        (nat queue *
          ((((event_data option) list) set * (nat, nat) sum) queue *
            (nat *
              (bool list *
                (bool list *
                  (((event_data option) list) set *
                    ((((event_data option) list), nat) mapping *
                      ((((event_data option) list), (nat, nat) sum) mapping dq *
                        (nat dq *
                          ((event_data option) list) set list))))))))));;

type 'a udmstate_ext =
  Udmstate_ext of nat * nat * udformula * nat * nat list * nat mbuf_t * 'a;;

type 'a x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod =
  Abs_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod of
    ('a option * ('a list * 'a list));;

let rec id x = (fun xa -> xa) x;;

let rec cmp (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then LT
          else (if eq _A1 x y then EQ else GT));;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nata then x else nth xs (minus_nata n one_nata));;

let rec rev_prepend x0 ys = match x0, ys with [], ys -> ys
                      | x :: xs, ys -> rev_prepend xs (x :: ys);;

let rec rev xs = rev_prepend xs [];;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec zip xs ys = match xs, ys with [], ys -> []
              | xs, [] -> []
              | x :: xs, y :: ys -> (x, y) :: zip xs ys;;

let rec rbt_fold_key
  f x1 s = match f, x1, s with f, Empty, s -> s
    | f, Branch (c, l, k, v, r), s ->
        rbt_fold_key f r (f k (rbt_fold_key f l s));;

let rec foldb _A f t = rbt_fold_key f (impl_ofa _A t);;

let rec bind (_A1, _A2) (_B1, _B2, _B3)
  x0 f = match x0, f with
    RBT_set rbt, f ->
      (match ccompare _A2
        with None ->
          failwith "bind RBT_set: ccompare = None"
            (fun _ -> bind (_A1, _A2) (_B1, _B2, _B3) (RBT_set rbt) f)
        | Some _ ->
          foldb _A2 (comp (sup_seta (_B1, _B2)) f) rbt
            (bot_set (_B1, _B2, _B3)))
    | DList_set dxs, f ->
        (match ceq _A1
          with None ->
            failwith "bind DList_set: ceq = None"
              (fun _ -> bind (_A1, _A2) (_B1, _B2, _B3) (DList_set dxs) f)
          | Some _ ->
            foldc _A1 (comp (sup_seta (_B1, _B2)) f) dxs
              (bot_set (_B1, _B2, _B3)))
    | Set_Monad xs, f -> fold (comp (sup_seta (_B1, _B2)) f) xs (Set_Monad []);;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nata then x :: xs
          else drop (minus_nata n one_nata) xs);;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nata then []
          else x :: take (minus_nata n one_nata) xs);;

let rec rep_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
  (Abs_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod x) =
    x;;

let rec sel12
  xa = Abs_queue
         (let (_, x2) =
            rep_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
              xa
            in
           x2);;

let rec sel11
  xa = (let (x1, _) =
          rep_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
            xa
          in
         x1);;

let rec rep_isom x = (sel11 x, sel12 x);;

let rec rep_queue (Abs_queue x) = x;;

let rec pop_t
  = function ([], []) -> (None, ([], []))
    | ([], [y]) -> (Some y, ([], []))
    | ([], y :: v :: va) -> (let z :: ys = rev (v :: va) in (Some z, (ys, [y])))
    | (x :: xs, ys) -> (Some x, (xs, ys));;

let rec pop_aux
  xa = Abs_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
         (pop_t (rep_queue xa));;

let rec pop x = rep_isom (pop_aux x);;

let rec mapa f x1 = match f, x1 with f, [] -> []
               | f, x21 :: x22 -> f x21 :: mapa f x22;;

let rec fun_upda equal f aa b a = (if equal aa a then b else f a);;

let rec balance_right
  a k x xa3 = match a, k, x, xa3 with
    a, k, x, Branch (R, b, s, y, c) ->
      Branch (R, a, k, x, Branch (B, b, s, y, c))
    | Branch (B, a, k, x, b), s, y, Empty ->
        balance (Branch (R, a, k, x, b)) s y Empty
    | Branch (B, a, k, x, b), s, y, Branch (B, va, vb, vc, vd) ->
        balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z, Empty ->
        Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, balance (paint R a) k x b, s, y,
               Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
    | Empty, k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Empty), k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh)), k, x, Empty -> Empty
    | Empty, k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Empty), k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl)), k, x,
        Branch (B, va, vb, vc, vd)
        -> Empty;;

let rec balance_left
  x0 s y c = match x0, s, y, c with
    Branch (R, a, k, x, b), s, y, c ->
      Branch (R, Branch (B, a, k, x, b), s, y, c)
    | Empty, k, x, Branch (B, a, s, y, b) ->
        balance Empty k x (Branch (R, a, s, y, b))
    | Branch (B, va, vb, vc, vd), k, x, Branch (B, a, s, y, b) ->
        balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
    | Empty, k, x, Branch (R, Branch (B, a, s, y, b), t, z, c) ->
        Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (B, a, s, y, b), t, z, c)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
               balance b t z (paint R c))
    | Empty, k, x, Empty -> Empty
    | Empty, k, x, Branch (R, Empty, vb, vc, vd) -> Empty
    | Empty, k, x, Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd) -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Empty -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Branch (R, Empty, vf, vg, vh) -> Empty
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)
        -> Empty;;

let rec combinea
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combinea b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combinea b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combinea (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combinea b (Branch (B, va, vb, vc, vd)));;

let rec rbt_comp_del
  c x xa2 = match c, x, xa2 with c, x, Empty -> Empty
    | c, x, Branch (uu, a, y, s, b) ->
        (match c x y with Eqa -> combinea a b
          | Lt -> rbt_comp_del_from_left c x a y s b
          | Gt -> rbt_comp_del_from_right c x a y s b)
and rbt_comp_del_from_left
  c x xa2 y s b = match c, x, xa2, y, s, b with
    c, x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (rbt_comp_del c x (Branch (B, lt, z, v, rt))) y s b
    | c, x, Empty, y, s, b -> Branch (R, rbt_comp_del c x Empty, y, s, b)
    | c, x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, rbt_comp_del c x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_comp_del_from_right
  c x a y s xa5 = match c, x, a, y, s, xa5 with
    c, x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (rbt_comp_del c x (Branch (B, lt, z, v, rt)))
    | c, x, a, y, s, Empty -> Branch (R, a, y, s, rbt_comp_del c x Empty)
    | c, x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, rbt_comp_del c x (Branch (R, va, vb, vc, vd)));;

let rec rbt_comp_delete c k t = paint B (rbt_comp_del c k t);;

let rec deleteb _A
  xb xc =
    Mapping_RBTa (rbt_comp_delete (the (ccompare _A)) xb (impl_ofa _A xc));;

let rec list_remove1
  equal x xa2 = match equal, x, xa2 with equal, x, [] -> []
    | equal, x, y :: xs ->
        (if equal x y then xs else y :: list_remove1 equal x xs);;

let rec removea _A
  xb xc = Abs_dlist (list_remove1 (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec insert (_A1, _A2)
  xa x1 = match xa, x1 with
    xa, Complement x -> Complement (remove (_A1, _A2) xa x)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "insert RBT_set: ccompare = None"
              (fun _ -> insert (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (insertb _A2 x () rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "insert DList_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (inserta _A1 x dxs))
    | x, Set_Monad xs -> Set_Monad (x :: xs)
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "insert Collect_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upda eq a x true))
and remove (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Complement a -> Complement (insert (_A1, _A2) x a)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "remove RBT_set: ccompare = None"
              (fun _ -> remove (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (deleteb _A2 x rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "remove DList_set: ceq = None"
              (fun _ -> remove (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (removea _A1 x dxs))
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "remove Collect: ceq = None"
              (fun _ -> remove (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upda eq a x false));;

let rec image (_A1, _A2) (_B1, _B2, _B3)
  h x1 = match h, x1 with
    h, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "image RBT_set: ccompare = None"
            (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) h (RBT_set rbt))
        | Some _ ->
          foldb _A2 (comp (insert (_B1, _B2)) h) rbt (bot_set (_B1, _B2, _B3)))
    | g, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "image DList_set: ceq = None"
              (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) g (DList_set dxs))
          | Some _ ->
            foldc _A1 (comp (insert (_B1, _B2)) g) dxs
              (bot_set (_B1, _B2, _B3)))
    | f, Complement (Complement b) -> image (_A1, _A2) (_B1, _B2, _B3) f b
    | f, Collect_set a ->
        failwith "image Collect_set"
          (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) f (Collect_set a))
    | f, Set_Monad xs -> Set_Monad (mapa f xs);;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec set_aux (_A1, _A2)
  = function Set_Monada -> (fun a -> Set_Monad a)
    | Set_Choose ->
        (match ccompare _A2
          with None ->
            (match ceq _A1 with None -> (fun a -> Set_Monad a)
              | Some _ ->
                foldl (fun s x -> insert (_A1, _A2) x s)
                  (DList_set (emptyb _A1)))
          | Some _ ->
            foldl (fun s x -> insert (_A1, _A2) x s) (RBT_set (emptyc _A2)))
    | impl ->
        foldl (fun s x -> insert (_A1, _A2) x s) (set_empty (_A1, _A2) impl);;

let rec set (_A1, _A2, _A3)
  xs = set_aux (_A1, _A2) (of_phantom (set_impl _A3)) xs;;

let rec cpos
  cs l =
    set (ceq_nat, ccompare_nat, set_impl_nat)
      (filtera (fun i -> member (ceq_nat, ccompare_nat) (nth cs i) l)
        (upt zero_nata (size_lista cs)));;

let rec add_to_rbt_comp (_B1, _B2, _B3)
  c = (fun (a, b) t ->
        (match rbt_comp_lookup c t a
          with None ->
            rbt_comp_insert c a (insert (_B1, _B2) b (bot_set (_B1, _B2, _B3)))
              t
          | Some x -> rbt_comp_insert c a (insert (_B1, _B2) b x) t));;

let rec cluster_rbt_comp (_B1, _B2, _B3)
  c f t =
    folda (fun b _ ta ->
            (match f b with None -> ta
              | Some a -> add_to_rbt_comp (_B1, _B2, _B3) c (a, b) ta))
      t Empty;;

let rec mapping_of_cluster (_B1, _B2, _B3) _A
  xb xc =
    Mapping_RBTa (cluster_rbt_comp (_B1, _B2, _B3) (the (ccompare _A)) xb xc);;

let rec cluster (_A1, _A2, _A3) _B
  f (RBT_set t) =
    (match ccompare _B
      with None ->
        failwith "cluster: ccompare = None"
          (fun _ -> cluster (_A1, _A2, _A3) _B f (RBT_set t))
      | Some _ ->
        (match ccompare _A2
          with None ->
            failwith "cluster: ccompare = None"
              (fun _ -> cluster (_A1, _A2, _A3) _B f (RBT_set t))
          | Some _ ->
            RBT_Mapping
              (mapping_of_cluster (_A1, _A2, _A3) _B f (impl_ofa _A2 t))));;

let rec dproj x0 xs = match x0, xs with [], xs -> []
                | true :: bs, x :: xs -> x :: dproj bs xs
                | false :: bs, x :: xs -> dproj bs xs
                | b :: bs, [] -> [];;

let rec didx (_A1, _A2)
  msk t =
    cluster ((ceq_list _A1), (ccompare_list _A2), set_impl_list)
      (ccompare_list _A2) (comp (fun a -> Some a) (dproj msk)) t;;

let tt : 'a formula = Eq (Const (EInt Z.zero), Const (EInt Z.zero));;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec those
  = function [] -> Some []
    | x :: xs ->
        (match x with None -> None
          | Some y -> map_option (fun a -> y :: a) (those xs));;

let rec map_of _A
  x0 k = match x0, k with [], k -> None
    | (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k);;

let rec funpow
  n f = (if equal_nata n zero_nata then id
          else comp f (funpow (minus_nata n one_nata) f));;

let wild : 'a regex = Skip one_nata;;

let rec filter (_A1, _A2) p a = inf_seta (_A1, _A2) a (Collect_set p);;

let rec intervala (_A1, _A2)
  a b = (if less _A2.linorder_interval.order_linorder.preorder_order.ord_preorder
              a b
          then a :: intervala (_A1, _A2)
                      (plus _A2.comm_semiring_1_cancel_interval.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
                        a (one _A2.comm_semiring_1_cancel_interval.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral))
                      b
          else (if eq _A1 a b then [a] else []));;

let rec atLeastLessThan (_A1, _A2, _A3, _A4, _A5)
  a b = (let d =
           minus _A4.comm_semiring_1_cancel_interval.semiring_1_cancel_comm_semiring_1_cancel.semiring_0_cancel_semiring_1_cancel.cancel_comm_monoid_add_semiring_0_cancel.cancel_ab_semigroup_add_cancel_comm_monoid_add.minus_cancel_ab_semigroup_add
             b (one _A4.comm_semiring_1_cancel_interval.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral)
           in
          (if less _A4.linorder_interval.order_linorder.preorder_order.ord_preorder
                d b
            then set (_A1, _A2, _A5) (intervala (_A3, _A4) a d)
            else bot_set (_A1, _A2, _A5)));;

let rec args_pos
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_pos;;

let rec args_ivl
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_ivl;;

let rec init_args i n l r pos agg = Args_ext (i, n, l, r, pos, agg, ());;

let rec dargs
  cs_R cs_L args =
    init_args (args_ivl args) (size_lista cs_R)
      (cpos cs_R (set (ceq_nat, ccompare_nat, set_impl_nat) cs_L))
      (atLeastLessThan
        (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat) zero_nata
        (size_lista cs_R))
      (args_pos args) None;;

let rec wide_mask_at
  i k cs =
    (if equal_nata k zero_nata then []
      else (match cs
             with [] -> false :: wide_mask_at (suc i) (minus_nata k one_nata) []
             | c :: csa ->
               (if equal_nata c i
                 then true :: wide_mask_at (suc i) (minus_nata k one_nata) csa
                 else false ::
                        wide_mask_at (suc i) (minus_nata k one_nata) cs)));;

let rec wide_mask n cs = wide_mask_at zero_nata n cs;;

let rec dtabc (_A1, _A2)
  n cs t =
    image ((ceq_list _A1), (ccompare_list _A2))
      ((ceq_list _A1), (ccompare_list _A2), set_impl_list)
      (dproj (wide_mask n cs)) t;;

let rec comp_fun_idem_apply (Abs_comp_fun_idem x) = x;;

let rec set_fold_cfi (_A1, _A2)
  f b x2 = match f, b, x2 with
    f, b, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold_cfi RBT_set: ccompare = None"
            (fun _ -> set_fold_cfi (_A1, _A2) f b (RBT_set rbt))
        | Some _ -> foldb _A2 (comp_fun_idem_apply f) rbt b)
    | f, b, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold_cfi DList_set: ceq = None"
              (fun _ -> set_fold_cfi (_A1, _A2) f b (DList_set dxs))
          | Some _ -> foldc _A1 (comp_fun_idem_apply f) dxs b)
    | f, b, Set_Monad xs -> fold (comp_fun_idem_apply f) xs b
    | f, b, Collect_set p ->
        failwith "set_fold_cfi not supported on Collect_set"
          (fun _ -> set_fold_cfi (_A1, _A2) f b (Collect_set p))
    | f, b, Complement a ->
        failwith "set_fold_cfi not supported on Complement"
          (fun _ -> set_fold_cfi (_A1, _A2) f b (Complement a));;

let rec sup_cfi _A
  = Abs_comp_fun_idem (sup _A.semilattice_sup_lattice.sup_semilattice_sup);;

let rec sup_setb (_A1, _A2, _A3, _A4, _A5)
  a = (if finite
            ((finite_UNIV_set _A1),
              (ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
              (ccompare_set (_A1, _A3, _A4, _A5)))
            a
        then set_fold_cfi
               ((ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
                 (ccompare_set (_A1, _A3, _A4, _A5)))
               (sup_cfi (lattice_set (_A2, _A3, _A4.ccompare_cproper_interval)))
               (bot_set (_A3, _A4.ccompare_cproper_interval, _A5)) a
        else failwith "Sup: infinite"
               (fun _ -> sup_setb (_A1, _A2, _A3, _A4, _A5) a));;

let rec fvi_trm
  b x1 = match b, x1 with
    b, Var x ->
      (if less_eq_nat b x
        then insert (ceq_nat, ccompare_nat) (minus_nata x b)
               (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
        else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
    | b, Const uu ->
        set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)
    | b, Plus (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, Minus (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, UMinus x -> fvi_trm b x
    | b, Mult (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, Div (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, Mod (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, F2i x -> fvi_trm b x
    | b, I2f x -> fvi_trm b x;;

let rec fv_regex (_B1, _B2, _B3)
  fv x1 = match fv, x1 with fv, Skip n -> bot_set (_B1, _B2, _B3)
    | fv, Test phi -> fv phi
    | fv, Plusa (r, s) ->
        sup_seta (_B1, _B2) (fv_regex (_B1, _B2, _B3) fv r)
          (fv_regex (_B1, _B2, _B3) fv s)
    | fv, Times (r, s) ->
        sup_seta (_B1, _B2) (fv_regex (_B1, _B2, _B3) fv r)
          (fv_regex (_B1, _B2, _B3) fv s)
    | fv, Star r -> fv_regex (_B1, _B2, _B3) fv r;;

let rec fvi
  b x1 = match b, x1 with
    b, Pred (r, ts) ->
      sup_setb
        (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
          set_impl_nat)
        (image (ceq_trm, ccompare_trm)
          ((ceq_set
             (cenum_nat, ceq_nat,
               cproper_interval_nat.ccompare_cproper_interval)),
            (ccompare_set
              (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat)),
            set_impl_set)
          (fvi_trm b) (set (ceq_trm, ccompare_trm, set_impl_trm) ts))
    | b, Let (p, phi, psi) -> fvi b psi
    | b, Frz (p, phi, psi) -> fvi b psi
    | b, LetPast (p, phi, psi) -> fvi b psi
    | b, Eq (t1, t2) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b t1) (fvi_trm b t2)
    | b, Less (t1, t2) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b t1) (fvi_trm b t2)
    | b, LessEq (t1, t2) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b t1) (fvi_trm b t2)
    | b, Neg phi -> fvi b phi
    | b, Or (phi, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, And (phi, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, Ands phi_s ->
        (let xs = mapa (fvi b) phi_s in
          sup_setb
            (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
              set_impl_nat)
            (image
              ((ceq_set
                 (cenum_nat, ceq_nat,
                   cproper_interval_nat.ccompare_cproper_interval)),
                (ccompare_set
                  (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)))
              ((ceq_set
                 (cenum_nat, ceq_nat,
                   cproper_interval_nat.ccompare_cproper_interval)),
                (ccompare_set
                  (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)),
                set_impl_set)
              (fun x -> x)
              (set ((ceq_set
                      (cenum_nat, ceq_nat,
                        cproper_interval_nat.ccompare_cproper_interval)),
                     (ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat)),
                     set_impl_set)
                xs)))
    | b, Exists (t, phi) -> fvi (suc b) phi
    | b, Agg (y, omega, tys, f, phi) ->
        sup_seta (ceq_nat, ccompare_nat)
          (sup_seta (ceq_nat, ccompare_nat)
            (fvi (plus_nata b (size_lista tys)) phi)
            (fvi_trm (plus_nata b (size_lista tys)) f))
          (if less_eq_nat b y
            then insert (ceq_nat, ccompare_nat) (minus_nata y b)
                   (set_empty (ceq_nat, ccompare_nat)
                     (of_phantom set_impl_nata))
            else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
    | b, Prev (i, phi) -> fvi b phi
    | b, Next (i, phi) -> fvi b phi
    | b, Since (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, Until (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, Trigger (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, Release (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, MatchF (i, r) ->
        fv_regex (ceq_nat, ccompare_nat, set_impl_nat) (fvi b) r
    | b, MatchP (i, r) ->
        fv_regex (ceq_nat, ccompare_nat, set_impl_nat) (fvi b) r
    | b, TP t -> fvi_trm b t
    | b, TS t -> fvi_trm b t;;

let rec semilattice_set_apply (Abs_semilattice_set x) = x;;

let rec is_emptyc _A
  xa = (match impl_ofa _A xa with Empty -> true
         | Branch (_, _, _, _, _) -> false);;

let rec rBT_Impl_fold1
  f x1 = match f, x1 with f, Empty -> failwith "undefined"
    | f, Branch (c, Empty, k, v, r) -> folda (fun ka _ -> f ka) r k
    | f, Branch (ca, Branch (c, l, ka, va, ra), k, v, r) ->
        folda (fun kb _ -> f kb) r
          (f k (rBT_Impl_fold1 f (Branch (c, l, ka, va, ra))));;

let rec fold1 _A x xc = rBT_Impl_fold1 x (impl_ofa _A xc);;

let rec nulla _A xa = null (list_of_dlist _A xa);;

let rec tla = function [] -> []
              | x21 :: x22 -> x22;;

let rec tl _A xa = Abs_dlist (tla (list_of_dlist _A xa));;

let rec hda (x21 :: x22) = x21;;

let rec hd _A xa = hda (list_of_dlist _A xa);;

let rec set_fold1 (_A1, _A2, _A3)
  f x1 = match f, x1 with
    f, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold1 RBT_set: ccompare = None"
            (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
        | Some _ ->
          (if is_emptyc _A2 rbt
            then failwith "set_fold1 RBT_set: empty set"
                   (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
            else fold1 _A2 (semilattice_set_apply f) rbt))
    | f, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold1 DList_set: ceq = None"
              (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
          | Some _ ->
            (if nulla _A1 dxs
              then failwith "set_fold1 DList_set: empty set"
                     (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
              else foldc _A1 (semilattice_set_apply f) (tl _A1 dxs)
                     (hd _A1 dxs)))
    | f, Set_Monad (x :: xs) -> fold (semilattice_set_apply f) xs x
    | f, Collect_set p ->
        failwith "set_fold1: Collect_set"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Collect_set p))
    | f, Complement a ->
        failwith "set_fold1: Complement"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Complement a));;

let rec max_sls _A
  = Abs_semilattice_set (max _A.order_linorder.preorder_order.ord_preorder);;

let rec maxa (_A1, _A2, _A3, _A4)
  a = set_fold1 (_A1, _A2, _A3) (max_sls _A4) a;;

let rec nfv
  phi = maxa (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
          (insert (ceq_nat, ccompare_nat) zero_nata
            (image (ceq_nat, ccompare_nat) (ceq_nat, ccompare_nat, set_impl_nat)
              suc (fvi zero_nata phi)));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec mTimesR
  r s = image (ceq_mregex, ccompare_mregex)
          (ceq_mregex, ccompare_mregex, set_impl_mregex)
          (fun ra -> MTimes (ra, s)) r;;

let rec lpd
  = function
    MSkip n ->
      (if equal_nata n zero_nata
        then set_empty (ceq_mregex, ccompare_mregex)
               (of_phantom set_impl_mregexa)
        else insert (ceq_mregex, ccompare_mregex)
               (MSkip (minus_nata n one_nata))
               (set_empty (ceq_mregex, ccompare_mregex)
                 (of_phantom set_impl_mregexa)))
    | MTestPos phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MTestNeg phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MPlus (r, s) -> sup_seta (ceq_mregex, ccompare_mregex) (lpd r) (lpd s)
    | MTimes (r, s) ->
        sup_seta (ceq_mregex, ccompare_mregex) (mTimesR (lpd r) s) (lpd s)
    | MStar r -> mTimesR (lpd r) (MStar r);;

let rec mTimesL
  r s = image (ceq_mregex, ccompare_mregex)
          (ceq_mregex, ccompare_mregex, set_impl_mregex)
          (fun a -> MTimes (r, a)) s;;

let rec rpd
  = function
    MSkip n ->
      (if equal_nata n zero_nata
        then set_empty (ceq_mregex, ccompare_mregex)
               (of_phantom set_impl_mregexa)
        else insert (ceq_mregex, ccompare_mregex)
               (MSkip (minus_nata n one_nata))
               (set_empty (ceq_mregex, ccompare_mregex)
                 (of_phantom set_impl_mregexa)))
    | MTestPos phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MTestNeg phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MPlus (r, s) -> sup_seta (ceq_mregex, ccompare_mregex) (rpd r) (rpd s)
    | MTimes (r, s) ->
        sup_seta (ceq_mregex, ccompare_mregex) (mTimesL r (rpd s)) (rpd r)
    | MStar r -> mTimesL (MStar r) (rpd r);;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let empty : ('a, 'b) alist = Alist [];;

let rec dmerge x0 xs ys = match x0, xs, ys with [], xs, ys -> []
                 | MLft :: p, x :: xs, ys -> x :: dmerge p xs ys
                 | MRgt :: p, xs, y :: ys -> y :: dmerge p xs ys
                 | MBth :: p, x :: xs, y :: ys -> x :: dmerge p xs ys
                 | MRgt :: p, xs, [] -> []
                 | MBth :: p, [], ys -> []
                 | MBth :: p, xs, [] -> []
                 | MLft :: p, [], ys -> []
                 | m :: p, [], [] -> [];;

let rec once i phi = Since (tt, i, phi);;

let all : i = Abs_I ((fun _ -> true), ((fun _ -> true), false));;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec map
  f x1 = match f, x1 with f, Empty -> Empty
    | f, Branch (c, lt, k, v, rt) -> Branch (c, map f lt, k, f k v, map f rt);;

let rec mapb _A xb xc = Mapping_RBTa (map xb (impl_ofa _A xc));;

let rec impl_of (Alist x) = x;;

let rec keysc (_A1, _A2, _A3) xa = set (_A1, _A2, _A3) (mapa fst (impl_of xa));;

let rec keys (_A1, _A2, _A3, _A4)
  = function RBT_Mapping t -> RBT_set (mapb _A3 (fun _ _ -> ()) t)
    | Assoc_List_Mapping al -> keysc (_A2, _A3, _A4) al
    | Mapping m -> collect _A1 (fun k -> not (is_none (m k)));;

let rec lPDs_aux
  s = (let sa =
         sup_seta (ceq_mregex, ccompare_mregex) s
           (bind (ceq_mregex, ccompare_mregex)
             (ceq_mregex, ccompare_mregex, set_impl_mregex) s lpd)
         in
        (if less_eq_set (cenum_mregex, ceq_mregex, ccompare_mregex) sa s then s
          else lPDs_aux sa));;

let rec lPDs
  r = lPDs_aux
        (insert (ceq_mregex, ccompare_mregex) r
          (set_empty (ceq_mregex, ccompare_mregex)
            (of_phantom set_impl_mregexa)));;

let rec rPDs_aux
  s = (let sa =
         sup_seta (ceq_mregex, ccompare_mregex) s
           (bind (ceq_mregex, ccompare_mregex)
             (ceq_mregex, ccompare_mregex, set_impl_mregex) s rpd)
         in
        (if less_eq_set (cenum_mregex, ceq_mregex, ccompare_mregex) sa s then s
          else rPDs_aux sa));;

let rec rPDs
  r = rPDs_aux
        (insert (ceq_mregex, ccompare_mregex) r
          (set_empty (ceq_mregex, ccompare_mregex)
            (of_phantom set_impl_mregexa)));;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec image_filter (_A1, _A2) (_B1, _B2, _B3)
  h x1 = match h, x1 with
    h, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "Option.image_filter RBT_set: ccompare = None"
            (fun _ -> image_filter (_A1, _A2) (_B1, _B2, _B3) h (RBT_set rbt))
        | Some _ ->
          foldb _A2
            (fun x a ->
              (match h x with None -> a | Some y -> insert (_B1, _B2) y a))
            rbt (bot_set (_B1, _B2, _B3)))
    | g, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "Option.image_filter DList_set: ceq = None"
              (fun _ ->
                image_filter (_A1, _A2) (_B1, _B2, _B3) g (DList_set dxs))
          | Some _ ->
            foldc _A1
              (fun x a ->
                (match g x with None -> a | Some y -> insert (_B1, _B2) y a))
              dxs (bot_set (_B1, _B2, _B3)))
    | f, Set_Monad xs -> Set_Monad (map_filter f xs);;

let rec these (_A1, _A2, _A3)
  a = image_filter ((ceq_option _A1), (ccompare_option _A2)) (_A1, _A2, _A3)
        (fun x -> x) a;;

let rec exhaustive_above_fusion
  proper_interval g y s =
    (if has_next g s
      then (let (x, sa) = next g s in
             not (proper_interval (Some y) (Some x)) &&
               exhaustive_above_fusion proper_interval g x sa)
      else not (proper_interval (Some y) None));;

let rec exhaustive_fusion
  proper_interval g s =
    has_next g s &&
      (let (x, sa) = next g s in
        not (proper_interval None (Some x)) &&
          exhaustive_above_fusion proper_interval g x sa);;

let rec list_remdups
  equal x1 = match equal, x1 with equal, [] -> []
    | equal, x :: xs ->
        (if list_member equal xs x then list_remdups equal xs
          else x :: list_remdups equal xs);;

let rec length _A xa = size_lista (list_of_dlist _A xa);;

let rec card (_A1, _A2, _A3)
  = function
    Complement a ->
      (let aa = card (_A1, _A2, _A3) a in
       let s = of_phantom (card_UNIV _A1) in
        (if less_nat zero_nata s then minus_nata s aa
          else (if finite (_A1.finite_UNIV_card_UNIV, _A2, _A3) a then zero_nata
                 else failwith "card Complement: infinite"
                        (fun _ -> card (_A1, _A2, _A3) (Complement a)))))
    | Set_Monad xs ->
        (match ceq _A2
          with None ->
            failwith "card Set_Monad: ceq = None"
              (fun _ -> card (_A1, _A2, _A3) (Set_Monad xs))
          | Some eq -> size_lista (list_remdups eq xs))
    | RBT_set rbt ->
        (match ccompare _A3
          with None ->
            failwith "card RBT_set: ccompare = None"
              (fun _ -> card (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> size_lista (keysb _A3 rbt))
    | DList_set dxs ->
        (match ceq _A2
          with None ->
            failwith "card DList_set: ceq = None"
              (fun _ -> card (_A1, _A2, _A3) (DList_set dxs))
          | Some _ -> length _A2 dxs);;

let rec is_UNIV (_A1, _A2, _A3)
  = function
    RBT_set rbt ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "is_UNIV RBT_set: ccompare = None"
            (fun _ -> is_UNIV (_A1, _A2, _A3) (RBT_set rbt))
        | Some _ ->
          of_phantom (finite_UNIV _A1.finite_UNIV_card_UNIV) &&
            exhaustive_fusion (cproper_interval _A3) rbt_keys_generator
              (init _A3.ccompare_cproper_interval rbt))
    | a -> (let aa = of_phantom (card_UNIV _A1) in
            let b = card (_A1, _A2, _A3.ccompare_cproper_interval) a in
             (if less_nat zero_nata aa then equal_nata aa b
               else (if less_nat zero_nata b then false
                      else failwith "is_UNIV called on infinite type and set"
                             (fun _ -> is_UNIV (_A1, _A2, _A3) a))));;

let rec is_empty (_A1, _A2, _A3)
  = function Complement a -> is_UNIV (_A1, _A2, _A3) a
    | RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "is_empty RBT_set: ccompare = None"
              (fun _ -> is_empty (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> is_emptyc _A3.ccompare_cproper_interval rbt)
    | DList_set dxs ->
        (match ceq _A2
          with None ->
            failwith "is_empty DList_set: ceq = None"
              (fun _ -> is_empty (_A1, _A2, _A3) (DList_set dxs))
          | Some _ -> nulla _A2 dxs)
    | Set_Monad xs -> null xs;;

let rec map_regex
  f x1 = match f, x1 with f, Skip x1 -> Skip x1
    | f, Test x2 -> Test (f x2)
    | f, Plusa (x31, x32) -> Plusa (map_regex f x31, map_regex f x32)
    | f, Times (x41, x42) -> Times (map_regex f x41, map_regex f x42)
    | f, Star x5 -> Star (map_regex f x5);;

let rec map_formula
  f x1 = match f, x1 with f, Pred (x11, x12) -> Pred (x11, x12)
    | f, Let (x21, x22, x23) -> Let (x21, map_formula f x22, map_formula f x23)
    | f, Frz (x31, x32, x33) -> Frz (x31, map_formula f x32, map_formula f x33)
    | f, LetPast (x41, x42, x43) ->
        LetPast (x41, map_formula f x42, map_formula f x43)
    | f, Eq (x51, x52) -> Eq (x51, x52)
    | f, Less (x61, x62) -> Less (x61, x62)
    | f, LessEq (x71, x72) -> LessEq (x71, x72)
    | f, Neg x8 -> Neg (map_formula f x8)
    | f, Or (x91, x92) -> Or (map_formula f x91, map_formula f x92)
    | f, And (x101, x102) -> And (map_formula f x101, map_formula f x102)
    | f, Ands x11a -> Ands (mapa (map_formula f) x11a)
    | f, Exists (x121, x122) -> Exists (f x121, map_formula f x122)
    | f, Agg (x131, x132, x133, x134, x135) ->
        Agg (x131, map_prod id f x132, mapa f x133, x134, map_formula f x135)
    | f, Prev (x141, x142) -> Prev (x141, map_formula f x142)
    | f, Next (x151, x152) -> Next (x151, map_formula f x152)
    | f, Since (x161, x162, x163) ->
        Since (map_formula f x161, x162, map_formula f x163)
    | f, Until (x171, x172, x173) ->
        Until (map_formula f x171, x172, map_formula f x173)
    | f, Trigger (x181, x182, x183) ->
        Trigger (map_formula f x181, x182, map_formula f x183)
    | f, Release (x191, x192, x193) ->
        Release (map_formula f x191, x192, map_formula f x193)
    | f, MatchF (x201, x202) -> MatchF (x201, map_regex (map_formula f) x202)
    | f, MatchP (x211, x212) -> MatchP (x211, map_regex (map_formula f) x212)
    | f, TP x22a -> TP x22a
    | f, TS x23a -> TS x23a;;

let rec bindb m f = (match m with Inl a -> Inl a | Inr a -> f a);;

let rec map_sig f s = comp (map_option (mapa f)) s;;

let rec check_two_formulas
  check s e phi psi =
    bindb (check s e phi)
      (fun f ->
        bindb (check (map_sig f s) (comp f e) (map_formula f psi))
          (fun fa -> Inr (comp fa f)));;

let rec new_type_symbol
  t = (match t with TAny n -> TAny (suc n) | TNum n -> TNum (suc n)
        | TCst a -> TCst a);;

let rec equal_ty x0 x1 = match x0, x1 with TFloat, TString -> false
                   | TString, TFloat -> false
                   | TInt, TString -> false
                   | TString, TInt -> false
                   | TInt, TFloat -> false
                   | TFloat, TInt -> false
                   | TString, TString -> true
                   | TFloat, TFloat -> true
                   | TInt, TInt -> true;;

let rec equal_tysym x0 x1 = match x0, x1 with TNum x2, TCst x3 -> false
                      | TCst x3, TNum x2 -> false
                      | TAny x1, TCst x3 -> false
                      | TCst x3, TAny x1 -> false
                      | TAny x1, TNum x2 -> false
                      | TNum x2, TAny x1 -> false
                      | TCst x3, TCst y3 -> equal_ty x3 y3
                      | TNum x2, TNum y2 -> equal_nata x2 y2
                      | TAny x1, TAny y1 -> equal_nata x1 y1;;

let rec catch_error m f = (match m with Inl a -> f a | Inr a -> Inr a);;

let rec str_of_tysym = function TCst TInt -> "int"
                       | TCst TFloat -> "float"
                       | TCst TString -> "string"
                       | TNum uu -> "numeric"
                       | TAny uv -> "any";;

let rec update_env
  x e = (let (tnew, told) = x in
          (fun v -> (if equal_tysym v told then tnew else v)));;

let rec min_type
  x0 x1 = match x0, x1 with
    TNum a, TNum b ->
      Inr (if less_eq_nat a b then (TNum a, TNum b) else (TNum b, TNum a))
    | TAny a, TAny b ->
        Inr (if less_eq_nat a b then (TAny a, TAny b) else (TAny b, TAny a))
    | TNum v, TAny y -> Inr (TNum v, TAny y)
    | TCst v, TAny y -> Inr (TCst v, TAny y)
    | TAny y, TNum v -> Inr (TNum v, TAny y)
    | TAny y, TCst v -> Inr (TCst v, TAny y)
    | TCst TString, TNum uu -> Inl ""
    | TNum uv, TCst TString -> Inl ""
    | TCst TInt, TNum y -> Inr (TCst TInt, TNum y)
    | TCst TFloat, TNum y -> Inr (TCst TFloat, TNum y)
    | TNum y, TCst TInt -> Inr (TCst TInt, TNum y)
    | TNum y, TCst TFloat -> Inr (TCst TFloat, TNum y)
    | TCst x, TCst y ->
        (if equal_ty x y then Inr (TCst x, TCst y) else Inl "");;

let rec clash_propagate
  t1 t2 e =
    catch_error (bindb (min_type t1 t2) (fun k -> Inr (update_env k e)))
      (fun _ ->
        Inl ((("clash of types " ^ str_of_tysym t1) ^ " and ") ^
              str_of_tysym t2));;

let rec check_binop
  check_trm e typ t1 t2 exp_typ =
    bindb (clash_propagate exp_typ typ e)
      (fun f ->
        bindb (check_trm (comp f e) (f typ) t1)
          (fun fa ->
            bindb (check_trm (comp (comp fa f) e) (comp fa f typ) t2)
              (fun fb -> Inr (comp (comp fb fa) f))));;

let rec ty_of = function EInt uu -> TInt
                | EFloat uv -> TFloat
                | EString uw -> TString;;

let rec check_trm
  e typ x2 = match e, typ, x2 with e, typ, Var v -> clash_propagate (e v) typ e
    | e, typ, Const c -> clash_propagate (TCst (ty_of c)) typ e
    | e, typ, F2i t ->
        bindb (clash_propagate typ (TCst TInt) e)
          (fun f ->
            bindb (check_trm (comp f e) (TCst TFloat) t)
              (fun fa ->
                Inr (fun ta ->
                      (if equal_tysym ta typ then TCst TInt
                        else comp fa f ta))))
    | e, typ, I2f t ->
        bindb (clash_propagate typ (TCst TFloat) e)
          (fun f ->
            bindb (check_trm (comp f e) (TCst TInt) t)
              (fun fa ->
                Inr (fun ta ->
                      (if equal_tysym ta typ then TCst TFloat
                        else comp fa f ta))))
    | e, typ, UMinus t ->
        bindb (clash_propagate (TNum zero_nata) (new_type_symbol typ)
                (comp new_type_symbol e))
          (fun f ->
            bindb (check_trm (comp (comp f new_type_symbol) e)
                    (f (new_type_symbol typ)) t)
              (fun fa -> Inr (comp (comp fa f) new_type_symbol)))
    | e, typ, Plus (t1, t2) ->
        bindb (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Minus (t1, t2) ->
        bindb (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Mult (t1, t2) ->
        bindb (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Div (t1, t2) ->
        bindb (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Mod (t1, t2) -> check_binop check_trm e typ t1 t2 (TCst TInt);;

let rec check_comparison
  e t1 t2 =
    bindb (check_trm (comp new_type_symbol e) (TAny zero_nata) t1)
      (fun f ->
        bindb (check_trm (comp (comp f new_type_symbol) e) (f (TAny zero_nata))
                t2)
          (fun fa -> Inr (comp (comp fa f) new_type_symbol)));;

let rec agg_trm_tysym = function Agg_Sum -> TNum zero_nata
                        | Agg_Cnt -> TAny zero_nata
                        | Agg_Avg -> TNum zero_nata
                        | Agg_Med -> TNum zero_nata
                        | Agg_Min -> TAny zero_nata
                        | Agg_Max -> TAny zero_nata;;

let rec t_res_tysym x0 t = match x0, t with Agg_Sum, t -> t
                      | Agg_Cnt, uu -> TCst TInt
                      | Agg_Avg, uv -> TCst TFloat
                      | Agg_Med, uw -> TCst TFloat
                      | Agg_Min, t -> t
                      | Agg_Max, t -> t;;

let rec check_regex
  check s e x3 = match check, s, e, x3 with check, s, e, Skip l -> Inr id
    | check, s, e, Test phi -> check s e phi
    | check, sa, e, Plusa (r, s) ->
        bindb (check_regex check sa e r)
          (fun f ->
            bindb (check_regex check (map_sig f sa) (comp f e)
                    (map_regex (map_formula f) s))
              (fun fa -> Inr (comp fa f)))
    | check, sa, e, Times (r, s) ->
        bindb (check_regex check sa e r)
          (fun f ->
            bindb (check_regex check (map_sig f sa) (comp f e)
                    (map_regex (map_formula f) s))
              (fun fa -> Inr (comp fa f)))
    | check, s, e, Star r -> check_regex check s e r;;

let rec check_pred
  p e x2 x3 = match p, e, x2, x3 with
    p, e, trm :: trms, t :: ts ->
      bindb (check_trm e t trm)
        (fun f ->
          bindb (check_pred p (comp f e) trms (mapa f ts))
            (fun fa -> Inr (comp fa f)))
    | p, e, [], [] -> Inr id
    | p, e, [], v :: va -> Inl ("wrong arity for predicate " ^ (fun x -> x) p)
    | p, e, v :: va, [] -> Inl ("wrong arity for predicate " ^ (fun x -> x) p);;

let rec check_ands_f
  check s e =
    (fun phi f_op ->
      bindb f_op
        (fun f ->
          bindb (check (map_sig f s) (comp f e) (map_formula f phi))
            (fun fa -> Inr (comp fa f))));;

let rec check_ands
  check s e phi_s = foldr (check_ands_f check s e) phi_s (Inr id);;

let rec agg_tysenv
  e tys =
    (fun z ->
      (if less_nat z (size_lista tys) then nth tys z
        else e (minus_nata z (size_lista tys))));;

let rec tabulate
  f x n =
    (if equal_nata n zero_nata then []
      else f x :: tabulate f (suc x) (minus_nata n one_nata));;

let rec check
  s e x2 = match s, e, x2 with
    s, e, Pred (r, ts) ->
      (match s (r, size_lista ts)
        with None ->
          Inl (("unknown predicate " ^ (fun x -> x) r) ^ " in input formula")
        | Some a -> check_pred r e ts a)
    | s, e, Let (p, phi, psi) ->
        (let f0 = funpow (nfv phi) new_type_symbol in
          bindb (check (map_sig f0 s) (fun a -> TAny a) (map_formula f0 phi))
            (fun f1 ->
              bindb (check
                      (map_sig f1
                        (fun_upd (equal_prod equal_string8 equal_nat)
                          (map_sig f0 s) (p, nfv phi)
                          (Some (mapa (fun a -> TAny a)
                                  (upt zero_nata (nfv phi))))))
                      (comp (comp f1 f0) e) (map_formula (comp f1 f0) psi))
                (fun f2 -> Inr (comp (comp f2 f1) f0))))
    | s, e, Frz (p, phi, psi) ->
        (let f0 = funpow (nfv phi) new_type_symbol in
          bindb (check (map_sig f0 s) (fun a -> TAny a) (map_formula f0 phi))
            (fun f1 ->
              bindb (check
                      (map_sig f1
                        (fun_upd (equal_prod equal_string8 equal_nat)
                          (map_sig f0 s) (p, nfv phi)
                          (Some (mapa (fun a -> TAny a)
                                  (upt zero_nata (nfv phi))))))
                      (comp (comp f1 f0) e) (map_formula (comp f1 f0) psi))
                (fun f2 -> Inr (comp (comp f2 f1) f0))))
    | s, e, Eq (t1, t2) -> check_comparison e t1 t2
    | s, e, Less (t1, t2) -> check_comparison e t1 t2
    | s, e, LessEq (t1, t2) -> check_comparison e t1 t2
    | s, e, Neg phi -> check s e phi
    | s, e, Or (phi, psi) -> check_two_formulas check s e phi psi
    | s, e, And (phi, psi) -> check_two_formulas check s e phi psi
    | s, e, Ands phi_s -> check_ands check s e phi_s
    | s, e, Exists (t, phi) ->
        check s
          (fun n ->
            (if equal_nata n zero_nata then t else e (minus_nata n one_nata)))
          phi
    | s, e, Agg (y, (agg_type, d), tys, trm, phi) ->
        bindb (check_trm (comp new_type_symbol (agg_tysenv e tys))
                (agg_trm_tysym agg_type) trm)
          (fun f ->
            bindb (check (map_sig (comp f new_type_symbol) s)
                    (comp (comp f new_type_symbol) (agg_tysenv e tys))
                    (map_formula (comp f new_type_symbol) phi))
              (fun fa ->
                bindb (check_trm (comp (comp (comp fa f) new_type_symbol) e)
                        (comp fa f
                          (t_res_tysym agg_type (agg_trm_tysym agg_type)))
                        (Var y))
                  (fun fb ->
                    bindb (check_trm
                            (comp (comp (comp (comp fb fa) f) new_type_symbol)
                              e)
                            (comp (comp (comp fb fa) f) new_type_symbol d)
                            (Var y))
                      (fun fc ->
                        Inr (comp (comp (comp (comp fc fb) fa) f)
                              new_type_symbol)))))
    | s, e, Prev (i, phi) -> check s e phi
    | s, e, Next (i, phi) -> check s e phi
    | s, e, Since (phi, i, psi) -> check_two_formulas check s e phi psi
    | s, e, Until (phi, i, psi) -> check_two_formulas check s e phi psi
    | s, e, Trigger (phi, i, psi) -> check_two_formulas check s e phi psi
    | s, e, Release (phi, i, psi) -> check_two_formulas check s e phi psi
    | s, e, MatchF (i, r) -> check_regex check s e r
    | s, e, MatchP (i, r) -> check_regex check s e r
    | s, e, LetPast (p, phi, psi) ->
        (let f0 = funpow (nfv phi) new_type_symbol in
          bindb (check
                  (fun_upd (equal_prod equal_string8 equal_nat) (map_sig f0 s)
                    (p, nfv phi)
                    (Some (tabulate (fun a -> TAny a) zero_nata (nfv phi))))
                  (fun a -> TAny a) (map_formula f0 phi))
            (fun f1 ->
              bindb (check
                      (map_sig f1
                        (fun_upd (equal_prod equal_string8 equal_nat)
                          (map_sig f0 s) (p, nfv phi)
                          (Some (mapa (fun a -> TAny a)
                                  (upt zero_nata (nfv phi))))))
                      (comp (comp f1 f0) e) (map_formula (comp f1 f0) psi))
                (fun f2 -> Inr (comp (comp f2 f1) f0))))
    | s, e, TP t -> check_trm e (TCst TInt) t
    | s, e, TS t -> check_trm e (TCst TInt) t;;

let rec filterb xb xc = Alist (filtera xb (impl_of xc));;

let rec lookup _A xa = map_of _A (impl_of xa);;

let rec updatea _A xc xd xe = Alist (update _A xc xd (impl_of xe));;

let rec col_pos
  xa0 x = match xa0, x with [], x -> zero_nata
    | c :: cs, x -> (if equal_nata c x then zero_nata else suc (col_pos cs x));;

let rec dembed1
  p d = mapa (fun a -> (match a with None -> None | Some aa -> nth d aa)) p;;

let rec dembedp (_A1, _A2)
  p d = image ((ceq_list (ceq_option _A1)),
                (ccompare_list (ccompare_option _A2)))
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
            set_impl_list)
          (dembed1 p) d;;

let rec all_true bs = list_all id bs;;

let rec dnarrow (_A1, _A2)
  msk r =
    (if all_true msk then r
      else image ((ceq_list _A1), (ccompare_list _A2))
             ((ceq_list _A1), (ccompare_list _A2), set_impl_list) (dproj msk)
             r);;

let rec ins_pos cs y = size_lista (filtera (fun c -> less_nat c y) cs);;

let rec equal_mrg x0 x1 = match x0, x1 with MRgt, MBth -> false
                    | MBth, MRgt -> false
                    | MLft, MBth -> false
                    | MBth, MLft -> false
                    | MLft, MRgt -> false
                    | MRgt, MLft -> false
                    | MBth, MBth -> true
                    | MRgt, MRgt -> true
                    | MLft, MLft -> true;;

let rec no_left p = list_all (fun m -> not (equal_mrg m MLft)) p;;

let rec rem_col cs y = filtera (fun c -> not (equal_nata c y)) cs;;

let rec ecard (_A1, _A2, _A3)
  a = (if finite (_A1.finite_UNIV_card_UNIV, _A2, _A3) a
        then Enat (card (_A1, _A2, _A3) a) else Infinity_enat);;

let rec rep_I (Abs_I x) = x;;

let rec memL x = fst (rep_I x);;

let rec memR x = fst (snd (rep_I x));;

let rec superset _A xs = list_all (membera _A xs);;

let rec mapping_empty_choose _A
  = (match ccompare _A with None -> Assoc_List_Mapping empty
      | Some _ -> RBT_Mapping (emptyc _A));;

let rec mapping_empty _A = function Mapping_RBT -> RBT_Mapping (emptyc _A)
                           | Mapping_Assoc_List -> Assoc_List_Mapping empty
                           | Mapping_Mapping -> Mapping (fun _ -> None)
                           | Mapping_Choose -> mapping_empty_choose _A;;

let rec emptya (_A1, _A2) = mapping_empty _A1 (of_phantom (mapping_impl _A2));;

let rec norm_queue_t
  q = (match q with ([], []) -> q | ([], [_]) -> q
        | ([], l :: v :: va) -> (rev (v :: va), [l]) | (_ :: _, _ :: _) -> q);;

let rec norm_queue xa = Abs_queue (norm_queue_t (rep_queue xa));;

let rec hd_queue_t
  q = (match q with ([], []) -> None | ([], [l]) -> Some l
        | ([], _ :: v :: va) -> Some (last (v :: va))
        | (f :: _, _ :: _) -> Some f);;

let rec hd_queue x = hd_queue_t (rep_queue x);;

let rec safe_hd q = (let qa = norm_queue q in (hd_queue qa, qa));;

let rec ueq x0 ys = match x0, ys with [], ys -> null ys
              | x :: xs, [] -> false
              | x :: xs, y :: ys -> equal_event_dataa x y && ueq xs ys;;

let rec inorder = function Leaf -> []
                  | Node (l, (a, uu), r) -> inorder l @ a :: inorder r;;

let rec emb_plan
  cs_R cs_L =
    mapa (fun c ->
           (if membera equal_nat cs_L c then Some (col_pos cs_L c) else None))
      cs_R;;

let rec mrg_right_key = function [] -> []
                        | MLft :: p -> mrg_right_key p
                        | MRgt :: p -> false :: mrg_right_key p
                        | MBth :: p -> true :: mrg_right_key p;;

let rec mrg_left_key = function [] -> []
                       | MLft :: p -> false :: mrg_left_key p
                       | MRgt :: p -> mrg_left_key p
                       | MBth :: p -> true :: mrg_left_key p;;

let rec no_right p = list_all (fun m -> not (equal_mrg m MRgt)) p;;

let rec mrg_plan
  x0 ds = match x0, ds with [], ds -> mapa (fun _ -> MRgt) ds
    | c :: cs, [] -> MLft :: mrg_plan cs []
    | c :: cs, d :: ds ->
        (if less_nat c d then MLft :: mrg_plan cs (d :: ds)
          else (if less_nat d c then MRgt :: mrg_plan (c :: cs) ds
                 else MBth :: mrg_plan cs ds));;

let rec mk_djoin
  cs1 cs2 =
    (if equal_lista equal_nat cs1 cs2 then DJEq
      else (if null cs2 then DJEmp
             else (let p = mrg_plan cs1 cs2 in
                    (if no_right p then DJSub (mrg_left_key p)
                      else (if no_left p then DJSup (mrg_right_key p)
                             else DJGen (p, mrg_left_key p,
  mrg_right_key p))))));;

let rec set_cols a = csorted_list_of_set (ceq_nat, ccompare_nat) a;;

let rec smp_cols = function [] -> []
                   | Var y :: ts -> y :: smp_cols ts
                   | Const v :: ts -> []
                   | Plus (v, va) :: ts -> []
                   | Minus (v, va) :: ts -> []
                   | UMinus v :: ts -> []
                   | Mult (v, va) :: ts -> []
                   | Div (v, va) :: ts -> []
                   | Mod (v, va) :: ts -> []
                   | F2i v :: ts -> []
                   | I2f v :: ts -> [];;

let rec dmsk cs_R cs_L = mrg_left_key (mrg_plan cs_R cs_L);;

let rec partition
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, x :: xs ->
        (let (yes, no) = partition p xs in
          (if p x then (x :: yes, no) else (yes, x :: no)));;

let rec replicate
  n x = (if equal_nata n zero_nata then []
          else x :: replicate (minus_nata n one_nata) x);;

let rec delete_aux _A
  k x1 = match k, x1 with k, [] -> []
    | ka, (k, v) :: xs ->
        (if eq _A ka k then xs else (k, v) :: delete_aux _A ka xs);;

let rec deletea _A xb xc = Alist (delete_aux _A xb (impl_of xc));;

let rec delete (_A1, _A2)
  k x1 = match k, x1 with
    k, RBT_Mapping t ->
      (match ccompare _A1
        with None ->
          failwith "delete RBT_Mapping: ccompare = None"
            (fun _ -> delete (_A1, _A2) k (RBT_Mapping t))
        | Some _ -> RBT_Mapping (deleteb _A1 k t))
    | k, Assoc_List_Mapping al -> Assoc_List_Mapping (deletea _A2 k al)
    | k, Mapping m -> Mapping (fun_upd _A2 m k None);;

let rec filterc _A
  p x1 = match p, x1 with
    p, RBT_Mapping t ->
      (match ccompare _A
        with None ->
          failwith "filter RBT_Mapping: ccompare = None"
            (fun _ -> filterc _A p (RBT_Mapping t))
        | Some _ -> RBT_Mapping (filtere _A (fun (a, b) -> p a b) t))
    | p, Assoc_List_Mapping al ->
        Assoc_List_Mapping (filterb (fun (a, b) -> p a b) al)
    | p, Mapping m ->
        Mapping
          (fun k ->
            (match m k with None -> None
              | Some v -> (if p k v then Some v else None)));;

let rec lookupa (_A1, _A2) = function RBT_Mapping t -> lookupb _A1 t
                             | Assoc_List_Mapping al -> lookup _A2 al;;

let rec updateb (_A1, _A2)
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t ->
      (match ccompare _A1
        with None ->
          failwith "update RBT_Mapping: ccompare = None"
            (fun _ -> updateb (_A1, _A2) k v (RBT_Mapping t))
        | Some _ -> RBT_Mapping (insertb _A1 k v t))
    | k, v, Assoc_List_Mapping al -> Assoc_List_Mapping (updatea _A2 k v al)
    | k, v, Mapping m -> Mapping (fun_upd _A2 m k (Some v));;

let ed_impl_of_v :
  ((((event_data option) list), unit) mapping_rbt ->
    (((event_data option) list), unit) rbt)
    boxed
  = Box (impl_ofa (ccompare_list (ccompare_option ccompare_event_data)));;

let rec ed_comparator
  x0 x1 = match x0, x1 with [], [] -> Eqa
    | [], y :: ys -> Lt
    | x :: xs, [] -> Gt
    | None :: xs, None :: ys -> ed_comparator xs ys
    | None :: xs, Some b :: ys -> Lt
    | Some a :: xs, None :: ys -> Gt
    | Some a :: xs, Some b :: ys ->
        (match comparator_event_data a b with Eqa -> ed_comparator xs ys
          | Lt -> Lt | Gt -> Gt);;

let rec ed_rbtc_ins
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (match ed_comparator k x with Eqa -> Branch (B, l, x, f k y v, r)
          | Lt -> balance (ed_rbtc_ins f k v l) x y r
          | Gt -> balance l x y (ed_rbtc_ins f k v r))
    | f, k, v, Branch (R, l, x, y, r) ->
        (match ed_comparator k x with Eqa -> Branch (R, l, x, f k y v, r)
          | Lt -> Branch (R, ed_rbtc_ins f k v l, x, y, r)
          | Gt -> Branch (R, l, x, y, ed_rbtc_ins f k v r));;

let rec ed_rbtc_insert_with_key f k v t = paint B (ed_rbtc_ins f k v t);;

let rec ed_rbtc_insert
  k v t = ed_rbtc_insert_with_key (fun _ _ nv -> nv) k v t;;

let rec unbox (Box x) = x;;

let rec ed_rbt_insert
  xc xd xe = Mapping_RBTa (ed_rbtc_insert xc xd (unbox ed_impl_of_v xe));;

let ed_remove_v :
  ((event_data option) list ->
    ((event_data option) list) set -> ((event_data option) list) set)
    boxed
  = Box (remove
          ((ceq_list (ceq_option ceq_event_data)),
            (ccompare_list (ccompare_option ccompare_event_data))));;

let rec ed_insert
  xa x1 = match xa, x1 with
    xa, Complement x -> Complement (unbox ed_remove_v xa x)
    | x, RBT_set rbt -> RBT_set (ed_rbt_insert x () rbt)
    | x, DList_set dxs ->
        DList_set (inserta (ceq_list (ceq_option ceq_event_data)) x dxs)
    | x, Set_Monad xs -> Set_Monad (x :: xs)
    | x, Collect_set a ->
        Collect_set
          (fun_upda (equality_list (equality_option equal_event_dataa)) a x
            true);;

let ed_bot : ((event_data option) list) set
  = RBT_set (emptyc (ccompare_list (ccompare_option ccompare_event_data)));;

let rec ed_singleton_table
  n i x =
    ed_insert
      (tabulate (fun j -> (if equal_nata i j then Some x else None)) zero_nata
        n)
      ed_bot;;

let rec ed_unit_table n = ed_insert (replicate n None) ed_bot;;

let rec eq_rel
  n uu uv = match n, uu, uv with
    n, Const x, Const y ->
      (if equal_event_dataa x y then ed_unit_table n else ed_bot)
    | n, Var x, Const y -> ed_singleton_table n x y
    | n, Const x, Var y -> ed_singleton_table n y x
    | n, Var v, Var va -> failwith "undefined"
    | n, Var v, Plus (va, vb) -> failwith "undefined"
    | n, Var v, Minus (va, vb) -> failwith "undefined"
    | n, Var v, UMinus va -> failwith "undefined"
    | n, Var v, Mult (va, vb) -> failwith "undefined"
    | n, Var v, Div (va, vb) -> failwith "undefined"
    | n, Var v, Mod (va, vb) -> failwith "undefined"
    | n, Var v, F2i va -> failwith "undefined"
    | n, Var v, I2f va -> failwith "undefined"
    | n, Plus (v, va), uv -> failwith "undefined"
    | n, Minus (v, va), uv -> failwith "undefined"
    | n, UMinus v, uv -> failwith "undefined"
    | n, Mult (v, va), uv -> failwith "undefined"
    | n, Div (v, va), uv -> failwith "undefined"
    | n, Mod (v, va), uv -> failwith "undefined"
    | n, F2i v, uv -> failwith "undefined"
    | n, I2f v, uv -> failwith "undefined"
    | n, uu, Plus (v, va) -> failwith "undefined"
    | n, uu, Minus (v, va) -> failwith "undefined"
    | n, uu, UMinus v -> failwith "undefined"
    | n, uu, Mult (v, va) -> failwith "undefined"
    | n, uu, Div (v, va) -> failwith "undefined"
    | n, uu, Mod (v, va) -> failwith "undefined"
    | n, uu, F2i v -> failwith "undefined"
    | n, uu, I2f v -> failwith "undefined";;

let rec is_emptya
  x = (match rep_queue x with ([], []) -> true | ([], _ :: _) -> false
        | (_ :: _, _) -> false);;

let rec tl_queue_t
  q = (match q with ([], []) -> q | ([], [_]) -> ([], [])
        | ([], l :: v :: va) -> (tla (rev (v :: va)), [l])
        | (_ :: asa, ls) -> (asa, ls));;

let rec tl_queue xa = Abs_queue (tl_queue_t (rep_queue xa));;

let rec restrict_aux
  i a x2 = match i, a, x2 with i, a, [] -> []
    | i, a, x :: xs ->
        (if member (ceq_nat, ccompare_nat) i a then x else None) ::
          restrict_aux (suc i) a xs;;

let rec restrict a v = restrict_aux zero_nata a v;;

let rec all_interval (_A1, _A2)
  p a b =
    (if less _A2.linorder_interval.order_linorder.preorder_order.ord_preorder a
          b
      then p a &&
             all_interval (_A1, _A2) p
               (plus _A2.comm_semiring_1_cancel_interval.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
                 a (one _A2.comm_semiring_1_cancel_interval.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral))
               b
      else true) &&
      (if eq _A1 a b then p a else true);;

let rec wf_tuple
  n v x =
    equal_nata (size_lista x) n &&
      (let d = minus_nata n one_nata in
        (if less_nat d n
          then all_interval (equal_nat, interval_nat)
                 (fun i ->
                   equal_boola (is_none (nth x i))
                     (not (member (ceq_nat, ccompare_nat) i v)))
                 zero_nata d
          else true));;

let rec entriesa _A xa = entries (impl_ofa _A xa);;

let rec set_of_idx _A (_B1, _B2, _B3)
  (RBT_Mapping t) =
    (match ccompare _A
      with None ->
        failwith "set_of_idx RBT_Mapping: ccompare = None"
          (fun _ -> set_of_idx _A (_B1, _B2, _B3) (RBT_Mapping t))
      | Some _ ->
        fold (fun p -> sup_seta (_B1, _B2) (snd p)) (entriesa _A t)
          (bot_set (_B1, _B2, _B3)));;

let rec dsemi_idx (_A1, _A2)
  msk pos idx x =
    set_of_idx (ccompare_list _A2)
      ((ceq_list _A1), (ccompare_list _A2), set_impl_list)
      (filterc (ccompare_list _A2)
        (fun k _ ->
          equal_boola (member ((ceq_list _A1), (ccompare_list _A2)) k x) pos)
        idx);;

let rec upd_cfi (_A1, _A2)
  xa = Abs_comp_fun_idem (fun a -> updateb (_A1, _A2) a (xa a));;

let rec upd_set (_A1, _A2, _A3, _A4)
  m f a =
    (if finite (_A1, _A2, _A3) a
      then set_fold_cfi (_A2, _A3) (upd_cfi (_A3, _A4) f) m a
      else failwith "upd_set: infinite"
             (fun _ -> upd_set (_A1, _A2, _A3, _A4) m f a));;

let edl_upd_set_nat_v :
  (((event_data list), nat) mapping ->
    (event_data list -> nat) ->
      (event_data list) set -> ((event_data list), nat) mapping)
    boxed
  = Box (upd_set
          (finite_UNIV_list, (ceq_list ceq_event_data),
            (ccompare_list ccompare_event_data),
            (equal_list equal_event_data)));;

let edl_mfilter_nat_v :
  ((event_data list -> nat -> bool) ->
    ((event_data list), nat) mapping -> ((event_data list), nat) mapping)
    boxed
  = Box (filterc (ccompare_list ccompare_event_data));;

let edl_mempty_nat : ((event_data list), nat) mapping
  = RBT_Mapping (emptyc (ccompare_list ccompare_event_data));;

let edl_impl_of_nat_v :
  (((event_data list), nat) mapping_rbt -> ((event_data list), nat) rbt) boxed
  = Box (impl_ofa (ccompare_list ccompare_event_data));;

let rec edl_comparator
  x0 x1 = match x0, x1 with [], [] -> Eqa
    | [], y :: ys -> Lt
    | x :: xs, [] -> Gt
    | x :: xs, y :: ys ->
        (match comparator_event_data x y with Eqa -> edl_comparator xs ys
          | Lt -> Lt | Gt -> Gt);;

let rec edl_rbtc_lookup
  x0 k = match x0, k with Empty, k -> None
    | Branch (cc, l, x, y, r), k ->
        (match edl_comparator k x with Eqa -> Some y | Lt -> edl_rbtc_lookup l k
          | Gt -> edl_rbtc_lookup r k);;

let rec edl_rbt_lookup_nat t k = edl_rbtc_lookup (unbox edl_impl_of_nat_v t) k;;

let rec edl_lookup_nat
  = function RBT_Mapping t -> edl_rbt_lookup_nat t
    | Assoc_List_Mapping al -> lookup (equal_list equal_event_data) al;;

let rec takedropWhile_queue
  f q = (match safe_hd q with (None, qa) -> (qa, [])
          | (Some a, qa) ->
            (if f a
              then (let (qb, asa) = takedropWhile_queue f (tl_queue qa) in
                     (qb, a :: asa))
              else (qa, [])));;

let rec dropWhile_queue
  f q = (match safe_hd q with (None, qa) -> qa
          | (Some a, qa) ->
            (if f a then dropWhile_queue f (tl_queue qa) else qa));;

let rec shift_end (_B1, _B2, _B3)
  i nt to_table (data_prev, (data_in, (tuple_in, tuple_in_keys))) =
    (let data_preva =
       dropWhile_queue (fun (t, _) -> not (memR i (minus_nata nt t))) data_prev
       in
     let (data_ina, in_discard) =
       takedropWhile_queue (fun (t, _) -> not (memR i (minus_nata nt t)))
         data_in
       in
     let (tuple_ina, tuple_in_keysa) =
       fold (fun (t, x) (tuple_ina, tuple_in_keysa) ->
              (filterc _B2
                 (fun asa _ ->
                   not (member (_B1, _B2) asa (to_table x) &&
                         equal_optiona equal_nat
                           (lookupa (_B2, _B3) tuple_ina asa) (Some t)))
                 tuple_ina,
                filter (_B1, _B2)
                  (fun asa ->
                    not (member (_B1, _B2) asa (to_table x) &&
                          equal_optiona equal_nat
                            (lookupa (_B2, _B3) tuple_ina asa) (Some t)))
                  tuple_in_keysa))
         in_discard (tuple_in, tuple_in_keys)
       in
      (data_preva, (data_ina, (in_discard, (tuple_ina, tuple_in_keysa)))));;

let rec flip_int_less_lower
  xa = Abs_I (if not (memL xa zero_nata)
               then ((fun _ -> true), ((fun i -> not (memL xa i)), true))
               else ((fun _ -> true), ((fun _ -> true), false)));;

let edl_impl_of_unit_v :
  (((event_data list), unit) mapping_rbt -> ((event_data list), unit) rbt) boxed
  = Box (impl_ofa (ccompare_list ccompare_event_data));;

let rec edl_rbt_lookup_unit
  t k = edl_rbtc_lookup (unbox edl_impl_of_unit_v t) k;;

let rec edl_rbt_member
  t x = equal_optiona equal_unit (edl_rbt_lookup_unit t x) (Some ());;

let rec edl_member
  x xa1 = match x, xa1 with
    x, Set_Monad xs -> list_member (equality_list equal_event_dataa) xs x
    | xa, Complement x -> not (edl_member xa x)
    | x, RBT_set rbt -> edl_rbt_member rbt x
    | x, DList_set dxs -> memberc (ceq_list ceq_event_data) dxs x
    | x, Collect_set a -> a x;;

let rec filter_comp_minus
  c t1 t2 =
    filtera (fun (k, _) -> is_none (rbt_comp_lookup c t2 k)) (entries t1);;

let rec rbt_baliR
  t1 ab bb x3 = match t1, ab, bb, x3 with
    t1, ab, bb, Branch (R, t2, aa, ba, Branch (R, t3, a, b, t4)) ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | t1, ab, bb, Branch (R, Branch (R, t2, aa, ba, t3), a, b, Empty) ->
        Branch
          (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, Empty))
    | t1, ab, bb,
        Branch (R, Branch (R, t2, aa, ba, t3), a, b, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, t1, ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, Branch (B, va, vb, vc, vd)))
    | t1, a, b, Empty -> Branch (B, t1, a, b, Empty)
    | t1, a, b, Branch (B, va, vb, vc, vd) ->
        Branch (B, t1, a, b, Branch (B, va, vb, vc, vd))
    | t1, a, b, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Empty))
    | t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | t1, a, b,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, t1, a, b,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)));;

let rec bheight
  = function Empty -> zero_nata
    | Branch (c, lt, k, v, rt) ->
        (if equal_color c B then suc (bheight lt) else bheight lt);;

let rec rbt_joinR
  l a b r =
    (if less_eq_nat (bheight l) (bheight r) then Branch (R, l, a, b, r)
      else (match l
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, la, ab, ba, rbt_joinR ra a b r)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliR la ab ba (rbt_joinR ra a b r)));;

let rec rbt_baliL
  x0 a b t4 = match x0, a, b, t4 with
    Branch (R, Branch (R, t1, ab, bb, t2), aa, ba, t3), a, b, t4 ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch (R, Empty, ab, bb, Branch (R, t2, aa, ba, t3)), a, b, t4 ->
        Branch
          (R, Branch (B, Empty, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch
        (R, Branch (B, va, vb, vc, vd), ab, bb, Branch (R, t2, aa, ba, t3)),
        a, b, t4
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, t4))
    | Empty, a, b, t2 -> Branch (B, Empty, a, b, t2)
    | Branch (B, va, vb, vc, vd), a, b, t2 ->
        Branch (B, Branch (B, va, vb, vc, vd), a, b, t2)
    | Branch (v, Empty, vb, vc, Empty), a, b, t2 ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), a, b, t2)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2 ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2 ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        a, b, t2
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               a, b, t2);;

let rec rbt_joinL
  l a b r =
    (if less_eq_nat (bheight r) (bheight l) then Branch (R, l, a, b, r)
      else (match r
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, rbt_joinL l a b la, ab, ba, ra)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliL (rbt_joinL l a b la) ab ba ra));;

let rec rbt_join
  l a b r =
    (let bhl = bheight l in
     let bhr = bheight r in
      (if less_nat bhr bhl then paint B (rbt_joinR l a b r)
        else (if less_nat bhl bhr then paint B (rbt_joinL l a b r)
               else Branch (B, l, a, b, r))));;

let rec rbt_split_comp
  c x1 k = match c, x1, k with c, Empty, k -> (Empty, (None, Empty))
    | c, Branch (uu, l, a, b, r), x ->
        (match c x a with Eqa -> (l, (Some b, r))
          | Lt ->
            (let (l1, (beta, l2)) = rbt_split_comp c l x in
              (l1, (beta, rbt_join l2 a b r)))
          | Gt ->
            (let (r1, (beta, r2)) = rbt_split_comp c r x in
              (rbt_join l a b r1, (beta, r2))));;

let rec small_rbt t = less_nat (bheight t) (nat_of_integer (Z.of_int 4));;

let rec is_rbt_empty
  t = (match t with Empty -> true | Branch (_, _, _, _, _) -> false);;

let rec rbt_split_min
  = function Empty -> failwith "undefined"
    | Branch (uu, l, a, b, r) ->
        (if is_rbt_empty l then (a, (b, r))
          else (let (aa, (ba, la)) = rbt_split_min l in
                 (aa, (ba, rbt_join la a b r))));;

let rec rbt_join2
  l r = (if is_rbt_empty r then l
          else (let (a, (b, c)) = rbt_split_min r in rbt_join l a b c));;

let rec comp_minus
  c t1 t2 =
    (if small_rbt t2 then folda (fun k _ -> rbt_comp_delete c k) t2 t1
      else (if small_rbt t1 then rbtreeify (filter_comp_minus c t1 t2)
             else (match t2 with Empty -> t1
                    | Branch (_, l2, a, _, r2) ->
                      (let (l1, (_, r1)) = rbt_split_comp c t1 a in
                        rbt_join2 (comp_minus c l1 l2)
                          (comp_minus c r1 r2)))));;

let rec rbt_comp_minus c t1 t2 = paint B (comp_minus c t1 t2);;

let rec edl_rbt_set_minus
  xb xc =
    Mapping_RBTa
      (rbt_comp_minus edl_comparator (unbox edl_impl_of_unit_v xb)
        (unbox edl_impl_of_unit_v xc));;

let rec edl_rbtc_ins
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (match edl_comparator k x with Eqa -> Branch (B, l, x, f k y v, r)
          | Lt -> balance (edl_rbtc_ins f k v l) x y r
          | Gt -> balance l x y (edl_rbtc_ins f k v r))
    | f, k, v, Branch (R, l, x, y, r) ->
        (match edl_comparator k x with Eqa -> Branch (R, l, x, f k y v, r)
          | Lt -> Branch (R, edl_rbtc_ins f k v l, x, y, r)
          | Gt -> Branch (R, l, x, y, edl_rbtc_ins f k v r));;

let rec edl_rbtc_insert_with_key f k v t = paint B (edl_rbtc_ins f k v t);;

let rec edl_rbtc_insert
  k v t = edl_rbtc_insert_with_key (fun _ _ nv -> nv) k v t;;

let rec edl_rbt_inter_list
  xb xc =
    Mapping_RBTa
      (fold (fun k -> edl_rbtc_insert k ())
        (filtera
          (fun x ->
            not (is_none (edl_rbtc_lookup (unbox edl_impl_of_unit_v xb) x)))
          xc)
        Empty);;

let rec map_filter_comp_inter
  c f t1 t2 =
    map_filter
      (fun (k, v) ->
        (match rbt_comp_lookup c t1 k with None -> None
          | Some va -> Some (k, f k va v)))
      (entries t2);;

let rec rbt_comp_inter_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then rbtreeify (map_filter_comp_inter c fa t1a t2a)
        else (match t1a with Empty -> Empty
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                  let l = rbt_comp_inter_swap_rec c f gammaa l1 l2 in
                  let r = rbt_comp_inter_swap_rec c f gammaa r1 r2 in
                   (match beta with None -> rbt_join2 l r
                     | Some ba -> rbt_join l a (fa a b ba) r)))));;

let rec rbt_comp_inter_with_key
  c f t1 t2 = paint B (rbt_comp_inter_swap_rec c f false t1 t2);;

let rec edl_rbt_meet_unit
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_inter_with_key edl_comparator xc (unbox edl_impl_of_unit_v xd)
        (unbox edl_impl_of_unit_v xe));;

let rec edl_rbt_insert_unit
  xc xd xe =
    Mapping_RBTa (edl_rbtc_insert xc xd (unbox edl_impl_of_unit_v xe));;

let rec rbt_comp_union_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then folda (rbt_comp_insert_with_key c fa) t2a t1a
        else (match t1a with Empty -> t2a
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                   rbt_join (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                     (match beta with None -> b | Some ca -> fa a b ca)
                     (rbt_comp_union_swap_rec c f gammaa r1 r2)))));;

let rec rbt_comp_union_with_key
  c f t1 t2 = paint B (rbt_comp_union_swap_rec c f false t1 t2);;

let rec edl_rbt_join_unit
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_union_with_key edl_comparator xc (unbox edl_impl_of_unit_v xd)
        (unbox edl_impl_of_unit_v xe));;

let rec edl_inter
  g ga = match g, ga with
    RBT_set rbt1, Set_Monad xs -> RBT_set (edl_rbt_inter_list rbt1 xs)
    | Set_Monad xs, RBT_set rbt1 -> RBT_set (edl_rbt_inter_list rbt1 xs)
    | Set_Monad xs, DList_set dxs2 ->
        DList_set
          (filterd (ceq_list ceq_event_data)
            (list_member (equality_list equal_event_dataa) xs) dxs2)
    | Set_Monad xs1, Set_Monad xs2 ->
        Set_Monad
          (filtera (list_member (equality_list equal_event_dataa) xs2) xs1)
    | RBT_set rbt, DList_set dxs ->
        RBT_set
          (edl_rbt_inter_list rbt (list_of_dlist (ceq_list ceq_event_data) dxs))
    | RBT_set rbt1, RBT_set rbt2 ->
        RBT_set (edl_rbt_meet_unit (fun _ _ -> id) rbt1 rbt2)
    | DList_set dxs1, Set_Monad xs ->
        DList_set
          (filterd (ceq_list ceq_event_data)
            (list_member (equality_list equal_event_dataa) xs) dxs1)
    | DList_set dxs1, DList_set dxs2 ->
        DList_set
          (filterd (ceq_list ceq_event_data)
            (memberc (ceq_list ceq_event_data) dxs2) dxs1)
    | DList_set dxs, RBT_set rbt ->
        RBT_set
          (edl_rbt_inter_list rbt (list_of_dlist (ceq_list ceq_event_data) dxs))
    | Complement ba, Complement b -> Complement (edl_union ba b)
    | g, RBT_set rbt2 ->
        RBT_set
          (filtere (ccompare_list ccompare_event_data)
            (comp (fun x -> edl_member x g) fst) rbt2)
    | RBT_set rbt1, g ->
        RBT_set
          (filtere (ccompare_list ccompare_event_data)
            (comp (fun x -> edl_member x g) fst) rbt1)
    | h, DList_set dxs2 ->
        DList_set
          (filterd (ceq_list ceq_event_data) (fun x -> edl_member x h) dxs2)
    | DList_set dxs1, h ->
        DList_set
          (filterd (ceq_list ceq_event_data) (fun x -> edl_member x h) dxs1)
    | i, Set_Monad xs -> Set_Monad (filtera (fun x -> edl_member x i) xs)
    | Set_Monad xs, i -> Set_Monad (filtera (fun x -> edl_member x i) xs)
    | j, Collect_set a -> Collect_set (fun x -> a x && edl_member x j)
    | Collect_set a, j -> Collect_set (fun x -> a x && edl_member x j)
and edl_union
  ba b = match ba, b with
    ba, Complement b -> Complement (edl_inter (uminus_set ba) b)
    | Complement ba, b -> Complement (edl_inter ba (uminus_set b))
    | RBT_set rbt1, RBT_set rbt2 ->
        RBT_set (edl_rbt_join_unit (fun _ _ -> id) rbt1 rbt2)
    | RBT_set rbt, DList_set dxs ->
        RBT_set
          (foldc (ceq_list ceq_event_data) (fun k -> edl_rbt_insert_unit k ())
            dxs rbt)
    | DList_set dxs, RBT_set rbt ->
        RBT_set
          (foldc (ceq_list ceq_event_data) (fun k -> edl_rbt_insert_unit k ())
            dxs rbt)
    | DList_set dxs1, DList_set dxs2 ->
        DList_set (union (ceq_list ceq_event_data) dxs1 dxs2)
    | Set_Monad zs, RBT_set rbt2 ->
        RBT_set (fold (fun k -> edl_rbt_insert_unit k ()) zs rbt2)
    | RBT_set rbt1, Set_Monad zs ->
        RBT_set (fold (fun k -> edl_rbt_insert_unit k ()) zs rbt1)
    | Set_Monad ws, DList_set dxs2 ->
        DList_set (fold (inserta (ceq_list ceq_event_data)) ws dxs2)
    | DList_set dxs1, Set_Monad ws ->
        DList_set (fold (inserta (ceq_list ceq_event_data)) ws dxs1)
    | Set_Monad xs, Set_Monad ys -> Set_Monad (xs @ ys)
    | b, Collect_set a -> Collect_set (fun x -> a x || edl_member x b)
    | Collect_set a, b -> Collect_set (fun x -> a x || edl_member x b);;

let rec edl_minus
  a b = match a, b with
    RBT_set rbt1, RBT_set rbt2 -> RBT_set (edl_rbt_set_minus rbt1 rbt2)
    | a, b -> edl_inter a (uminus_set b);;

let rec edl_filter p a = edl_inter a (Collect_set p);;

let rec de_dsemi
  msk pos a b =
    edl_filter (fun aa -> equal_boola (edl_member (dproj msk aa) b) pos) a;;

let edl_bot : (event_data list) set
  = RBT_set (emptyc (ccompare_list ccompare_event_data));;

let rec de_gsemi_join
  msk pos r l =
    (if list_all (fun i -> i) msk
      then (if pos then edl_inter r l else edl_minus r l)
      else (if list_all not msk
             then (if equal_boola pos (edl_member [] l) then r else edl_bot)
             else de_dsemi msk pos r l));;

let rec append_queue
  xb xc = Abs_queue (let (fs, ls) = rep_queue xc in (fs, xb :: ls));;

let empty_queue : 'a queue = Abs_queue ([], []);;

let rec de_gupdate_mmtauxa
  args nt idx_mid idx_oldest msk data_prev data_in tuple_in_once
    tuple_in_once_keys tuple_since_hist hist_sat since_sat =
    (let (_, (data_preva, (move, (tuple_in_oncea, tuple_in_once_keysa)))) =
       shift_end
         ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data),
           (equal_list equal_event_data))
         (flip_int_less_lower (args_ivl args)) nt fst
         (empty_queue, (data_prev, (tuple_in_once, tuple_in_once_keys)))
       in
     let move_len = size_lista move in
     let idx_mida = plus_nata idx_mid move_len in
     let (data_ina, drop) =
       takedropWhile_queue
         (fun (t, _) -> not (memR (args_ivl args) (minus_nata nt t))) data_in
       in
     let movea =
       filtera (fun (t, _) -> memR (args_ivl args) (minus_nata nt t)) move in
     let drop_prev_len = minus_nata move_len (size_lista movea) in
     let idx_oldesta =
       plus_nata (plus_nata idx_oldest (size_lista drop)) drop_prev_len in
     let data_inb = fold (fun (t, (_, r)) -> append_queue (t, r)) movea data_ina
       in
     let (tuple_since_hista, (hist_sata, (_, since_sata))) =
       fold (fun (_, (l, r))
              (tuple_since_hista, (hist_sata, (idx_move, since_sata))) ->
              (let tuple_since_histb =
                 unbox edl_mfilter_nat_v (fun asa _ -> edl_member asa r)
                   tuple_since_hista
                 in
               let hist_satb = edl_inter hist_sata r in
               let since_satb = edl_inter since_sata r in
                (unbox edl_upd_set_nat_v tuple_since_histb (fun _ -> idx_move)
                   (edl_filter
                     (fun k -> is_none (edl_lookup_nat tuple_since_histb k)) r),
                  (hist_satb,
                    (plus_nata idx_move one_nata,
                      edl_union since_satb
                        (de_gsemi_join msk (args_pos args) r l))))))
         move (tuple_since_hist, (hist_sat, (idx_mid, since_sat)))
       in
     let tuple_since_histb =
       (if equal_nata idx_mida idx_oldesta then edl_mempty_nat
         else tuple_since_hista)
       in
     let since_satb =
       (if equal_nata idx_mida idx_oldesta then edl_bot else since_sata) in
     let hist_satb =
       (match fst (safe_hd data_inb) with None -> edl_bot
         | Some db ->
           edl_union hist_sata
             (edl_filter
               (fun tuple ->
                 (match edl_lookup_nat tuple_since_histb tuple
                   with None -> false
                   | Some idx -> less_eq_nat idx idx_oldesta))
               (snd db)))
       in
      (idx_mida,
        (idx_oldesta,
          (data_preva,
            (data_inb,
              (tuple_in_oncea,
                (tuple_in_once_keysa,
                  (tuple_since_histb, (hist_satb, since_satb)))))))));;

let rec de_gupdate_mmtaux
  args nt l r =
    (fun (_, (idx_next,
               (idx_mid,
                 (idx_oldest,
                   (msk, (data_prev,
                           (data_in,
                             (tuple_in_once,
                               (tuple_in_once_keys,
                                 (tuple_since_hist,
                                   (hist_sat, since_sat)))))))))))
      -> (let (idx_mida,
                (idx_oldesta,
                  (data_preva,
                    (data_ina,
                      (tuple_in_oncea,
                        (tuple_in_once_keysa,
                          (tuple_since_hista, (hist_sata, since_sata))))))))
            = de_gupdate_mmtauxa args nt idx_mid idx_oldest msk data_prev
                data_in tuple_in_once tuple_in_once_keys tuple_since_hist
                hist_sat since_sat
            in
           (if memL (args_ivl args) zero_nata && memR (args_ivl args) zero_nata
             then (let tuple_since_histb =
                     unbox edl_mfilter_nat_v (fun asa _ -> edl_member asa r)
                       tuple_since_hista
                     in
                    (nt, (plus_nata idx_next one_nata,
                           (plus_nata idx_mida one_nata,
                             (idx_oldesta,
                               (msk, (data_preva,
                                       (append_queue (nt, r) data_ina,
 (tuple_in_oncea,
   (tuple_in_once_keysa,
     (unbox edl_upd_set_nat_v tuple_since_histb (fun _ -> idx_mida)
        (edl_filter (fun k -> is_none (edl_lookup_nat tuple_since_histb k)) r),
       ((if is_emptya data_ina then r else edl_inter hist_sata r),
         edl_union (edl_inter since_sata r)
           (de_gsemi_join msk (args_pos args) r l)))))))))))))
             else (nt, (plus_nata idx_next one_nata,
                         (idx_mida,
                           (idx_oldesta,
                             (msk, (append_queue (nt, (l, r)) data_preva,
                                     (data_ina,
                                       (unbox edl_upd_set_nat_v tuple_in_oncea
  (fun _ -> nt) l,
 (edl_union tuple_in_once_keysa l,
   (tuple_since_hista, (hist_sata, since_sata))))))))))))));;

let edl_is_empty_v : ((event_data list) set -> bool) boxed
  = Box (is_empty
          (card_UNIV_list, (ceq_list ceq_event_data),
            (cproper_interval_list ccompare_event_data)));;

let rec de_geps_lax
  msks guard phi_s x3 = match msks, guard, phi_s, x3 with
    msks, guard, phi_s, MSkip n ->
      (if equal_nata n zero_nata then guard else edl_bot)
    | msks, guard, phi_s, MTestPos i ->
        de_dsemi (nth msks i) true guard (nth phi_s i)
    | msks, guard, phi_s, MTestNeg i ->
        de_dsemi (nth msks i) false guard (nth phi_s i)
    | msks, guard, phi_s, MPlus (r, s) ->
        edl_union (de_geps_lax msks guard phi_s r)
          (de_geps_lax msks guard phi_s s)
    | msks, guard, phi_s, MTimes (r, s) ->
        edl_inter (de_geps_lax msks guard phi_s r)
          (de_geps_lax msks guard phi_s s)
    | msks, guard, phi_s, MStar r -> guard;;

let edl_remove_v :
  (event_data list -> (event_data list) set -> (event_data list) set) boxed
  = Box (remove
          ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data)));;

let rec edl_insert
  xa x1 = match xa, x1 with
    xa, Complement x -> Complement (unbox edl_remove_v xa x)
    | x, RBT_set rbt -> RBT_set (edl_rbt_insert_unit x () rbt)
    | x, DList_set dxs -> DList_set (inserta (ceq_list ceq_event_data) x dxs)
    | x, Set_Monad xs -> Set_Monad (x :: xs)
    | x, Collect_set a ->
        Collect_set (fun_upda (equality_list equal_event_dataa) a x true);;

let rec de_greps_strict
  msks phi_s x2 = match msks, phi_s, x2 with
    msks, phi_s, MSkip m ->
      (if equal_nata m zero_nata then edl_insert [] edl_bot else edl_bot)
    | msks, phi_s, MTestPos i -> nth phi_s i
    | msks, phi_s, MTestNeg i ->
        (if unbox edl_is_empty_v (nth phi_s i) then edl_insert [] edl_bot
          else edl_bot)
    | msks, phi_s, MPlus (r, s) ->
        edl_union (de_greps_strict msks phi_s r) (de_greps_strict msks phi_s s)
    | msks, phi_s, MTimes (r, s) ->
        de_geps_lax msks (de_greps_strict msks phi_s r) phi_s s
    | msks, phi_s, MStar r -> edl_insert [] edl_bot;;

let rec rbt_comp_bulkload
  c xs = foldr (fun (a, b) -> rbt_comp_insert c a b) xs Empty;;

let rec bulkload _A
  xa = Mapping_RBTa (rbt_comp_bulkload (the (ccompare _A)) xa);;

let rec de_gmrtabulate
  xs f =
    (match ccompare_mregexa
      with None ->
        failwith "gmrtabulate RBT_Mapping: ccompare = None"
          (fun _ -> de_gmrtabulate xs f)
      | Some _ ->
        RBT_Mapping
          (bulkload ccompare_mregex
            (map_filter
              (fun k ->
                (let fk = f k in
                  (if unbox edl_is_empty_v fk then None else Some (k, fk))))
              xs)));;

let rec lookup_default (_B1, _B2)
  d m k = (match lookupa (_B1, _B2) m k with None -> d | Some v -> v);;

let rec de_glookup
  x = lookup_default (ccompare_mregex, equal_mregex) edl_bot x;;

let rec de_grdelta
  msks kappa x phi_s xa4 = match msks, kappa, x, phi_s, xa4 with
    msks, kappa, x, phi_s, MSkip n ->
      (if equal_nata n zero_nata then edl_bot
        else de_glookup x (kappa (MSkip (minus_nata n one_nata))))
    | msks, kappa, x, phi_s, MTestPos i -> edl_bot
    | msks, kappa, x, phi_s, MTestNeg i -> edl_bot
    | msks, kappa, x, phi_s, MPlus (r, s) ->
        edl_union (de_grdelta msks kappa x phi_s r)
          (de_grdelta msks kappa x phi_s s)
    | msks, kappa, x, phi_s, MTimes (r, s) ->
        edl_union (de_grdelta msks (fun t -> kappa (MTimes (r, t))) x phi_s s)
          (de_geps_lax msks (de_grdelta msks kappa x phi_s r) phi_s s)
    | msks, kappa, x, phi_s, MStar r ->
        de_grdelta msks (fun t -> kappa (MTimes (MStar r, t))) x phi_s r;;

let rec de_gupdate_matchP
  msks i mr mrs rels nt aux =
    (let auxa =
       (match
         maps (fun (t, rel) ->
                (if memR i (minus_nata nt t)
                  then [(t, de_gmrtabulate mrs
                              (fun mra ->
                                edl_union (de_grdelta msks id rel rels mra)
                                  (if equal_nata t nt
                                    then de_greps_strict msks rels mra
                                    else edl_bot)))]
                  else []))
           aux
         with [] -> [(nt, de_gmrtabulate mrs (de_greps_strict msks rels))]
         | x :: auxa ->
           (if equal_nata (fst x) nt then x :: auxa
             else (nt, de_gmrtabulate mrs (de_greps_strict msks rels)) ::
                    x :: auxa))
       in
      (foldr (sup_seta
               ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data)))
         (maps (fun (t, rel) ->
                 (if memL i (minus_nata nt t) then [de_glookup rel mr] else []))
           auxa)
         edl_bot,
        auxa));;

let rec de_gldelta
  msks kappa x phi_s xa4 = match msks, kappa, x, phi_s, xa4 with
    msks, kappa, x, phi_s, MSkip n ->
      (if equal_nata n zero_nata then edl_bot
        else de_glookup x (kappa (MSkip (minus_nata n one_nata))))
    | msks, kappa, x, phi_s, MTestPos i -> edl_bot
    | msks, kappa, x, phi_s, MTestNeg i -> edl_bot
    | msks, kappa, x, phi_s, MPlus (r, s) ->
        edl_union (de_gldelta msks kappa x phi_s r)
          (de_gldelta msks kappa x phi_s s)
    | msks, kappa, x, phi_s, MTimes (r, s) ->
        edl_union (de_gldelta msks (fun t -> kappa (MTimes (t, s))) x phi_s r)
          (de_geps_lax msks (de_gldelta msks kappa x phi_s s) phi_s r)
    | msks, kappa, x, phi_s, MStar r ->
        de_gldelta msks (fun t -> kappa (MTimes (t, MStar r))) x phi_s r;;

let rec de_gupdate_matchF_step
  msks i mr mrs nt =
    (fun (t, (rels, rel)) (aux, x) ->
      (let y = de_gmrtabulate mrs (de_gldelta msks id x rels) in
        ((t, (rels,
               (if memL i (minus_nata nt t) && memR i (minus_nata nt t)
                 then edl_union rel (de_glookup y mr) else rel))) ::
           aux,
          y)));;

let rec de_gleps_strict
  msks phi_s x2 = match msks, phi_s, x2 with
    msks, phi_s, MSkip m ->
      (if equal_nata m zero_nata then edl_insert [] edl_bot else edl_bot)
    | msks, phi_s, MTestPos i -> nth phi_s i
    | msks, phi_s, MTestNeg i ->
        (if unbox edl_is_empty_v (nth phi_s i) then edl_insert [] edl_bot
          else edl_bot)
    | msks, phi_s, MPlus (r, s) ->
        edl_union (de_gleps_strict msks phi_s r) (de_gleps_strict msks phi_s s)
    | msks, phi_s, MTimes (r, s) ->
        de_geps_lax msks (de_gleps_strict msks phi_s s) phi_s r
    | msks, phi_s, MStar r -> edl_insert [] edl_bot;;

let rec de_gupdate_matchF_base
  msks i mr mrs rels nt =
    (let x = de_gmrtabulate mrs (de_gleps_strict msks rels) in
      ([(nt, (rels, (if memL i zero_nata then de_glookup x mr else edl_bot)))],
        x));;

let rec de_gupdate_matchF
  msks i mr mrs rels nt aux =
    fst (foldr (de_gupdate_matchF_step msks i mr mrs nt) aux
          (de_gupdate_matchF_base msks i mr mrs rels nt));;

let rec de_gresult_mmtaux
  args =
    (fun (_, (_, (_, (_, (_, (_, (_, (_, (tuple_in_once_keys,
   (_, (hist_sat, a)))))))))))
      -> edl_union (edl_union tuple_in_once_keys hist_sat) a);;

let rec de_gmmtaux_empty
  x = (fun (_, (_, (_, (_, (_, (_, (data_in, (_, (_, (_, (_, _))))))))))) ->
        is_emptya data_in)
        x;;

let rec linearize x = (let (fs, ls) = rep_queue x in fs @ rev ls);;

let rec rep_mbuf_t (MBuf2_t x) = linearize x;;

let rec de_geval_matchF
  i mr nt x3 = match i, mr, nt, x3 with i, mr, nt, [] -> ([], [])
    | i, mr, nt, (t, (rels, rel)) :: aux ->
        (if not (memR i (minus_nata nt t))
          then (let (xs, a) = de_geval_matchF i mr nt aux in (rel :: xs, a))
          else ([], (t, (rels, rel)) :: aux));;

let rec eval_constraint0
  xa0 x y = match xa0, x, y with MEq, x, y -> equal_event_dataa x y
    | MLess, x, y -> less_event_data x y
    | MLessEq, x, y -> less_eq_event_data x y;;

let rec uminus_event_data = function EInt x -> EInt (Z.neg x)
                            | EFloat x -> EFloat (Stdlib.(~-.) x)
                            | EString v -> failwith "undefined";;

let rec mod_to_zero
  x y = (let z =
           snd ((fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem
                  (Z.abs k) (Z.abs l))
                 x y)
           in
          (if Z.lt x Z.zero then Z.neg z else z));;

let rec modulo_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (mod_to_zero x y)
    | EFloat v, uv -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | uu, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec div_to_zero
  x y = (let z =
           fst ((fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem
                  (Z.abs k) (Z.abs l))
                 x y)
           in
          (if not (equal_boola (Z.lt x Z.zero) (Z.lt y Z.zero)) then Z.neg z
            else z));;

let rec divide_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (div_to_zero x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.(/.) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec times_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (Z.mul x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.( *. ) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec minus_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (Z.sub x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.(-.) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec plus_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (Z.add x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.(+.) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec integer_of_event_data = function EInt uu -> failwith "undefined"
                                | EFloat x -> Z.of_float x
                                | EString uv -> failwith "undefined";;

let rec double_of_event_data = function EInt x -> Z.to_float x
                               | EFloat uu -> failwith "undefined"
                               | EString uv -> failwith "undefined";;

let rec umeval_trm
  x0 v = match x0, v with Var x, v -> nth v x
    | Const x, v -> x
    | Plus (x, y), v -> plus_event_data (umeval_trm x v) (umeval_trm y v)
    | Minus (x, y), v -> minus_event_data (umeval_trm x v) (umeval_trm y v)
    | UMinus x, v -> uminus_event_data (umeval_trm x v)
    | Mult (x, y), v -> times_event_data (umeval_trm x v) (umeval_trm y v)
    | Div (x, y), v -> divide_event_data (umeval_trm x v) (umeval_trm y v)
    | Mod (x, y), v -> modulo_event_data (umeval_trm x v) (umeval_trm y v)
    | F2i x, v -> EInt (integer_of_event_data (umeval_trm x v))
    | I2f x, v -> EFloat (double_of_event_data (umeval_trm x v));;

let rec ueval_constraint
  conf x =
    (let (t1, (p, (c, t2))) = conf in
      equal_boola (eval_constraint0 c (umeval_trm t1 x) (umeval_trm t2 x)) p);;

let rec pop_queue_t
  q = (match q with ([], []) -> q | ([], [_]) -> ([], [])
        | ([], l :: v :: va) -> (tla (rev (v :: va)), [l])
        | (_ :: fs, ls) -> (fs, ls));;

let rec pop_queue xa = Abs_queue (pop_queue_t (rep_queue xa));;

let rec mbuf_t_tl (MBuf2_t xs) = MBuf2_t (pop_queue xs);;

let rec mbuf_t_hd (MBuf2_t xs) = hd_queue xs;;

let rec mbuf_t_cases
  b = (let a = mbuf_t_hd b in
        (a, (match a with None -> b | Some _ -> mbuf_t_tl b)));;

let rec prepend_queue_t
  a q = (let (fs, ls) = q in
          (match ls with [] -> (let [] = fs in ([], [a]))
            | _ :: _ -> (a :: fs, ls)));;

let rec prepend_queue xb xc = Abs_queue (prepend_queue_t xb (rep_queue xc));;

let rec mbuf_t_Cons x (MBuf2_t xs) = MBuf2_t (prepend_queue x xs);;

let rec binda m f = (fun () -> f (m ()) ());;

let rec mebuf2t_take_j
  f z buf t0 ts =
    (let (xs, ys) = buf in
      (match mbuf_t_cases ts
        with (None, tsa) -> (fun () -> (z, ((xs, ys), (t0, tsa))))
        | (Some t, tsa) ->
          (match mbuf_t_cases xs
            with (None, xsa) ->
              (fun () -> (z, ((xsa, ys), (t, mbuf_t_Cons t tsa))))
            | (Some x, xsa) ->
              (match mbuf_t_cases ys
                with (None, ysa) ->
                  (fun () ->
                    (z, ((mbuf_t_Cons x xsa, ysa), (t, mbuf_t_Cons t tsa))))
                | (Some y, ysa) ->
                  binda (f x y t z)
                    (fun za -> mebuf2t_take_j f za (xsa, ysa) t tsa)))));;

let edl_set_eq_v :
  ((event_data list) set -> (event_data list) set -> bool) boxed
  = Box (set_eq
          (cenum_list, (ceq_list ceq_event_data),
            (ccompare_list ccompare_event_data)));;

let rec append_queue_list
  xb xc = Abs_queue (let (fs, ls) = rep_queue xc in (fs, rev_prepend xb ls));;

let rec mbuf_t_append (MBuf2_t xs) ys = MBuf2_t (append_queue_list ys xs);;

let rec size_dformula
  = function DFail -> zero_nata
    | DRel x2 -> zero_nata
    | DPredS (x31, x32) -> zero_nata
    | DPredM (x41, x42, x43, x44) -> zero_nata
    | DAnd (x51, x52, x53, x54, x55) ->
        plus_nata (plus_nata (size_dformula x52) (size_dformula x54))
          (suc zero_nata)
    | DAnds (x61, x62, x63, x64) ->
        plus_nata (size_list size_dformula x63) (suc zero_nata)
    | DAndRel (x71, x72) -> plus_nata (size_dformula x71) (suc zero_nata)
    | DOr (x81, x82, x83) ->
        plus_nata (plus_nata (size_dformula x81) (size_dformula x82))
          (suc zero_nata)
    | DNeg x9 -> plus_nata (size_dformula x9) (suc zero_nata)
    | DExists (x101, x102) -> plus_nata (size_dformula x101) (suc zero_nata)
    | DAgg (x111, x112, x113, x114, x115, x116) ->
        plus_nata (size_dformula x116) (suc zero_nata)
    | DPrev (x121, x122, x123, x124, x125) ->
        plus_nata (size_dformula x122) (suc zero_nata)
    | DNext (x131, x132, x133, x134) ->
        plus_nata (size_dformula x132) (suc zero_nata)
    | DSince (x141, x142, x143, x144, x145) ->
        plus_nata (plus_nata (size_dformula x142) (size_dformula x143))
          (suc zero_nata)
    | DUntil (x151, x152, x153, x154, x155, x156, x157, x158) ->
        plus_nata (plus_nata (size_dformula x153) (size_dformula x154))
          (suc zero_nata)
    | DAndAssign (x161, x162, x163) ->
        plus_nata (size_dformula x163) (suc zero_nata)
    | DTP (x171, x172) -> zero_nata
    | DTS x18 -> zero_nata
    | DLet (x191, x192, x193, x194) ->
        plus_nata (plus_nata (size_dformula x193) (size_dformula x194))
          (suc zero_nata)
    | DFrz (x201, x202, x203, x204, x205, x206, x207, x208) ->
        plus_nata (plus_nata (size_dformula x203) (size_dformula x204))
          (suc zero_nata)
    | DLetPast (x211, x212, x213, x214, x215, x216) ->
        plus_nata (plus_nata (size_dformula x213) (size_dformula x214))
          (suc zero_nata)
    | DTrigger (x221, x222, x223, x224, x225, x226) ->
        plus_nata (plus_nata (size_dformula x222) (size_dformula x223))
          (suc zero_nata)
    | DAndTrigger (x231, x232, x233, x234, x235, x236, x237, x238, x239) ->
        plus_nata
          (plus_nata (plus_nata (size_dformula x232) (size_dformula x235))
            (size_dformula x236))
          (suc zero_nata)
    | DMatchP (x241, x242, x243, x244, x245, x246, x247, x248) ->
        plus_nata (size_list size_dformula x245) (suc zero_nata)
    | DMatchF (x251, x252, x253, x254, x255, x256, x257, x258, x259) ->
        plus_nata (size_list size_dformula x255) (suc zero_nata);;

let rec map_valuesa
  xb xc = Alist (mapa (fun (x, y) -> (x, xb x y)) (impl_of xc));;

let rec map_values _A
  f x1 = match f, x1 with
    f, RBT_Mapping t ->
      (match ccompare _A
        with None ->
          failwith "map_values RBT_Mapping: ccompare = None"
            (fun _ -> map_values _A f (RBT_Mapping t))
        | Some _ -> RBT_Mapping (mapb _A f t))
    | f, Assoc_List_Mapping al -> Assoc_List_Mapping (map_valuesa f al)
    | f, Mapping m -> Mapping (fun k -> map_option (f k) (m k));;

let rec letpast_meval0_h
  eval j i ys xs p ts db phi =
    binda (eval ts
             (updateb
               ((ccompare_prod ccompare_string8 ccompare_nat),
                 (equal_prod equal_string8 equal_nat))
               p xs db)
            phi)
      (fun r ->
        (if not (equal_nata (size_dformula (snd r)) (size_dformula phi))
          then (fun () -> ([], (zero_nata, (None, phi))))
          else (match fst r
                 with [] ->
                   (fun () ->
                     (ys @ fst r, (plus_nata i (size_lista xs), (None, snd r))))
                 | y :: _ ->
                   (if less_eq_nat j (suc (plus_nata i (size_lista xs)))
                     then (fun () ->
                            (ys @ fst r,
                              (plus_nata i (size_lista xs), (Some y, snd r))))
                     else letpast_meval0_h eval j (plus_nata i (size_lista xs))
                            (ys @ fst r) (fst r) p []
                            (map_values
                              (ccompare_prod ccompare_string8 ccompare_nat)
                              (fun _ _ -> []) db)
                            (snd r)))));;

let mbuf_t_empty : 'a mbuf_t = MBuf2_t empty_queue;;

let rec umatch
  x0 uv = match x0, uv with [], [] -> Some (fun _ -> None)
    | Const x :: ts, y :: ys ->
        (if equal_event_dataa x y then umatch ts ys else None)
    | Var x :: ts, y :: ys ->
        (match umatch ts ys with None -> None
          | Some f ->
            (match f x with None -> Some (fun_upd equal_nat f x (Some y))
              | Some z -> (if equal_event_dataa y z then Some f else None)))
    | Var vb :: va, [] -> None
    | Plus (vb, vc) :: va, uv -> None
    | Minus (vb, vc) :: va, uv -> None
    | UMinus vb :: va, uv -> None
    | Mult (vb, vc) :: va, uv -> None
    | Div (vb, vc) :: va, uv -> None
    | Mod (vb, vc) :: va, uv -> None
    | F2i vb :: va, uv -> None
    | I2f vb :: va, uv -> None
    | v :: va, [] -> None
    | [], v :: va -> None;;

let rec umatch_table
  tms cs x =
    these ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data),
            set_impl_list)
      (image ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data))
        ((ceq_option (ceq_list ceq_event_data)),
          (ccompare_option (ccompare_list ccompare_event_data)),
          (set_impl_option set_impl_list))
        (fun xa ->
          map_option (fun f -> mapa (fun c -> the (f c)) cs) (umatch tms xa))
        x);;

let rec freeze_meval0_h
  eval k x2 = match eval, k, x2 with eval, k, [] -> (fun () -> ([], []))
    | eval, k, alpha :: alpha_s ->
        binda (eval alpha)
          (fun r ->
            (match drop k (fst r) with [] -> (fun () -> ([], alpha :: alpha_s))
              | y :: _ ->
                binda (freeze_meval0_h eval (suc k) alpha_s)
                  (fun z -> (fun () -> (y :: fst z, snd z)))));;

let rec mebuf2_take
  f (xs, ys) =
    (match mbuf_t_cases xs with (None, xsa) -> ([], (xsa, ys))
      | (Some x, xsa) ->
        (match mbuf_t_cases ys
          with (None, ysa) -> ([], (mbuf_t_Cons x xsa, ysa))
          | (Some y, ysa) ->
            (let (zs, a) = mebuf2_take f (xsa, ysa) in (f x y :: zs, a))));;

let edl_rbt_fold_table_v :
  ((event_data list -> (event_data list) set -> (event_data list) set) ->
    ((event_data list), unit) mapping_rbt ->
      (event_data list) set -> (event_data list) set)
    boxed
  = Box (foldb (ccompare_list ccompare_event_data));;

let rec edl_image
  h (RBT_set rbt) =
    unbox edl_rbt_fold_table_v (fun x -> edl_insert (h x)) rbt edl_bot;;

let rec mebuf2_add
  xsa ysa (xs, ys) = (mbuf_t_append xs xsa, mbuf_t_append ys ysa);;

let rec mbuf_t_is_empty (MBuf2_t xs) = is_emptya xs;;

let rec mebufn_take_j
  f z buf =
    (if null buf || list_ex mbuf_t_is_empty buf then (fun () -> (z, buf))
      else binda (f (mapa (comp (comp the fst) mbuf_t_cases) buf))
             (fun x ->
               mebufn_take_j f (mbuf_t_append z [x])
                 (mapa (comp snd mbuf_t_cases) buf)));;

let rec mebuf2_take_j
  f buf =
    (let (xs, ys) = buf in
      (match mbuf_t_cases xs with (None, xsa) -> (fun () -> ([], (xsa, ys)))
        | (Some x, xsa) ->
          (match mbuf_t_cases ys
            with (None, ysa) -> (fun () -> ([], (mbuf_t_Cons x xsa, ysa)))
            | (Some y, ysa) ->
              binda (f x y)
                (fun z ->
                  binda (mebuf2_take_j f (xsa, ysa))
                    (fun r -> (fun () -> (z :: fst r, snd r)))))));;

let rec umebufnt_take
  f z buf t0 ts =
    (match mbuf_t_cases ts with (None, _) -> (z, (buf, (t0, ts)))
      | (Some t, tsa) ->
        (if list_ex mbuf_t_is_empty buf then (z, (buf, (t, mbuf_t_Cons t tsa)))
          else umebufnt_take f
                 (f (mapa (comp (comp the fst) mbuf_t_cases) buf) t z)
                 (mapa (comp snd mbuf_t_cases) buf) t tsa));;

let rec umebuf2T_take
  f z (xs, ys) ts =
    (match mbuf_t_cases ts with (None, tsa) -> (z, ((xs, ys), tsa))
      | (Some t, tsa) ->
        (match mbuf_t_cases xs
          with (None, xsa) -> (z, ((xsa, ys), mbuf_t_Cons t tsa))
          | (Some x, xsa) ->
            (match mbuf_t_cases ys
              with (None, ysa) ->
                (z, ((mbuf_t_Cons x xsa, ysa), mbuf_t_Cons t tsa))
              | (Some y, ysa) -> umebuf2T_take f (f x y t z) (xsa, ysa) tsa)));;

let rec list_of_option = function None -> []
                         | Some x -> [x];;

let rec umeprev_next
  i xs ts =
    (match mbuf_t_cases xs with (None, _) -> ([], (mbuf_t_empty, ts))
      | (Some x, xsa) ->
        (match mbuf_t_cases ts
          with (None, _) -> ([], (mbuf_t_Cons x xsa, mbuf_t_empty))
          | (Some t, tsa) ->
            (match mbuf_t_cases tsa
              with (None, _) ->
                ([], (mbuf_t_Cons x xsa, mbuf_t_Cons t mbuf_t_empty))
              | (Some ta, tsb) ->
                (let (ys, a) = umeprev_next i xsa (mbuf_t_Cons ta tsb) in
                  ((if memL i (minus_nata ta t) && memR i (minus_nata ta t)
                     then x else edl_bot) ::
                     ys,
                    a)))));;

let rec umebuf2S_add
  xsa ysa tsa (xs, (ys, (ts, skew))) =
    (mbuf_t_append xs xsa,
      (mbuf_t_append ys ysa, (mbuf_t_append ts tsa, skew)));;

let rec minus_keys (_A1, _A2, _A3)
  x m = filter (_A1, _A2)
          (fun xa ->
            (match lookupa (_A2, _A3) m xa with None -> true | Some _ -> false))
          x;;

let edl_minus_keys_v :
  ((event_data list) set ->
    ((event_data list), nat) mapping -> (event_data list) set)
    boxed
  = Box (minus_keys
          ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data),
            (equal_list equal_event_data)));;

let edl_mempty_table : ((event_data list), (event_data list) set) mapping
  = RBT_Mapping (emptyc (ccompare_list ccompare_event_data));;

let rec args_R
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_R;;

let rec args_L
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_L;;

let rec didx_live
  args =
    not (is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
          (args_L args)) &&
      not (set_eq (cenum_nat, ceq_nat, ccompare_nat) (args_L args)
            (args_R args));;

let rec de_gidx_upd
  args w = (if didx_live args then w () else edl_mempty_table);;

let rec join _A
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_union_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec combine _B
  f (RBT_Mapping t) (RBT_Mapping u) =
    (match ccompare _B
      with None ->
        failwith "combine RBT_Mapping: ccompare = None"
          (fun _ -> combine _B f (RBT_Mapping t) (RBT_Mapping u))
      | Some _ -> RBT_Mapping (join _B (fun _ -> f) t u));;

let rec didx_union (_A1, _A2)
  = combine (ccompare_list _A2)
      (sup_seta ((ceq_list _A1), (ccompare_list _A2)));;

let rec de_gadd_new_table_msaux
  args x
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (let xa = unbox edl_minus_keys_v x tuple_since in
       let tuple_sincea = unbox edl_upd_set_nat_v tuple_since (fun _ -> t) xa in
       let idx_sincea =
         de_gidx_upd args
           (fun _ ->
             didx_union (ceq_event_data, ccompare_event_data) idx_since
               (didx (ceq_event_data, ccompare_event_data) msk xa))
         in
        (if memL (args_ivl args) zero_nata
          then (t, (gc, (msk, (data_prev,
                                (append_queue (t, x) data_in,
                                  (edl_union table_in x,
                                    (de_gidx_upd args
                                       (fun _ ->
 didx_union (ceq_event_data, ccompare_event_data) idx_in
   (didx (ceq_event_data, ccompare_event_data) msk x)),
                                      (unbox edl_upd_set_nat_v tuple_in
 (fun _ -> t) x,
(idx_sincea, tuple_sincea)))))))))
          else (t, (gc, (msk, (append_queue (t, x) data_prev,
                                (data_in,
                                  (table_in,
                                    (idx_in,
                                      (tuple_in,
(idx_sincea, tuple_sincea)))))))))));;

let edl_csorted_list_of_set_v :
  ((event_data list) set -> (event_data list) list) boxed
  = Box (csorted_list_of_set
          ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data)));;

let rec edl_rbt_insert_nat
  xc xd xe = Mapping_RBTa (edl_rbtc_insert xc xd (unbox edl_impl_of_nat_v xe));;

let rec edl_update_nat
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t -> RBT_Mapping (edl_rbt_insert_nat k v t)
    | k, v, Assoc_List_Mapping al ->
        Assoc_List_Mapping (updatea (equal_list equal_event_data) k v al)
    | k, v, Mapping m ->
        Mapping (fun_upd (equal_list equal_event_data) m k (Some v));;

let rec de_gevt_add
  t cc =
    fold (fun ta (c, s) ->
           (match edl_lookup_nat c ta
             with None -> (edl_update_nat ta one_nata c, edl_insert ta s)
             | Some k -> (edl_update_nat ta (plus_nata k one_nata) c, s)))
      (unbox edl_csorted_list_of_set_v t) cc;;

let rec de_gadd_new_table_sevt
  args x aux =
    (let (t, (pend, (win, (cnt, cur)))) = aux in
      (if memL (args_ivl args) zero_nata
        then (let (cnta, cura) = de_gevt_add x (cnt, cur) in
               (t, (pend, (append_queue (t, x) win, (cnta, cura)))))
        else (t, (append_queue (t, x) pend, (win, (cnt, cur))))));;

let rec dgg_trm
  (Daggargs_ext (dgg_g0, dgg_op, dgg_trm, dgg_k, dgg_p, more)) = dgg_trm;;

let rec dgg_k
  (Daggargs_ext (dgg_g0, dgg_op, dgg_trm, dgg_k, dgg_p, more)) = dgg_k;;

let rec rep_wf_wbt _A (Abs_wf_wbt x) = x;;

let rec size_wbt = function Leaf -> zero_nata
                   | Node (uu, (uv, n), uw) -> n;;

let rec balanced1
  t1 t2 =
    less_eq_nat
      (times_nata (nat_of_integer (Z.of_int 10))
        (plus_nata (size_wbt t2) one_nata))
      (times_nata (nat_of_integer (Z.of_int 25))
        (plus_nata (size_wbt t1) one_nata));;

let rec single
  t1 t2 =
    less_nat
      (times_nata (nat_of_integer (Z.of_int 10))
        (plus_nata (size_wbt t1) one_nata))
      (times_nata (nat_of_integer (Z.of_int 14))
        (plus_nata (size_wbt t2) one_nata));;

let rec n
  l a r =
    Node (l, (a, plus_nata (plus_nata (size_wbt l) (size_wbt r)) one_nata), r);;

let rec rot1R aa a ba b c = n aa a (n ba b c);;

let rec rot2 aa a (Node (b1, (b, uu), b2)) ca c = n (n aa a b1) b (n b2 ca c);;

let rec rotateR
  (Node (aa, (a, uu), ba)) b c =
    (if single ba aa then rot1R aa a ba b c else rot2 aa a ba b c);;

let rec balanceR l a r = (if balanced1 r l then n l a r else rotateR l a r);;

let rec rot1L aa a ba b c = n (n aa a ba) b c;;

let rec rotateL
  aa a (Node (ba, (b, uu), c)) =
    (if single ba c then rot1L aa a ba b c else rot2 aa a ba b c);;

let rec balanceL l a r = (if balanced1 l r then n l a r else rotateL l a r);;

let rec insertc (_A1, _A2)
  x xa1 = match x, xa1 with x, Leaf -> Node (Leaf, (x, one_nata), Leaf)
    | x, Node (l, (a, n), r) ->
        (match cmp (_A1, _A2) x a
          with LT -> balanceR (insertc (_A1, _A2) x l) a r
          | EQ -> balanceR (insertc (_A1, _A2) x l) a r
          | GT -> balanceL l a (insertc (_A1, _A2) x r));;

let rec tree_insert (_A1, _A2)
  xb xc = Abs_wf_wbt (insertc (_A1, _A2) xb (rep_wf_wbt _A2 xc));;

let rec insert_treelist (_A1, _A2)
  x (Collapse y) = Collapse (tree_insert (_A1, _A2) x y);;

let rec empty_tree _A = Abs_wf_wbt Leaf;;

let rec empty_treelist _A = Collapse (empty_tree _A);;

let rec dinsert_rank
  args ty t (v, m) =
    (if v then (let g = drop (dgg_k args) t in
                let e = umeval_trm (dgg_trm args) t in
                let (va, l) =
                  (match
                    (lookupa
                       ((ccompare_list ccompare_event_data),
                         (equal_list equal_event_data))
                       m g,
                      (e, ty))
                    with (None, (EInt c, IntT)) ->
                      (true,
                        LInt (insert_treelist (equal_integer, linorder_integer)
                               c (empty_treelist linorder_integer)))
                    | (None, (EInt _, StringT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EString _, IntT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EString c, StringT)) ->
                      (true,
                        LString
                          (insert_treelist (equal_string8, linorder_string8) c
                            (empty_treelist linorder_string8)))
                    | (Some (LInt s), (EInt c, IntT)) ->
                      (true,
                        LInt (insert_treelist (equal_integer, linorder_integer)
                               c s))
                    | (Some (LInt _), (EInt _, StringT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LInt _), (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LInt _), (EString _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EInt _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EString _, IntT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString s), (EString c, StringT)) ->
                      (true,
                        LString
                          (insert_treelist (equal_string8, linorder_string8) c
                            s)))
                  in
                 (va, (if va
                        then updateb
                               ((ccompare_list ccompare_event_data),
                                 (equal_list equal_event_data))
                               g l m
                        else mapping_empty (ccompare_list ccompare_event_data)
                               (of_phantom mapping_impl_lista))))
      else (v, m));;

let rec dinsert_sum
  args t (v, m) =
    (if v then (let g = drop (dgg_k args) t in
                let e = umeval_trm (dgg_trm args) t in
                 (match
                   (lookupa
                      ((ccompare_list ccompare_event_data),
                        (equal_list equal_event_data))
                      m g,
                     e)
                   with (None, EInt i) ->
                     (true,
                       updateb
                         ((ccompare_list ccompare_event_data),
                           (equal_list equal_event_data))
                         g (one_nata, i) m)
                   | (None, EFloat _) ->
                     (false,
                       mapping_empty (ccompare_list ccompare_event_data)
                         (of_phantom mapping_impl_lista))
                   | (None, EString _) ->
                     (false,
                       mapping_empty (ccompare_list ccompare_event_data)
                         (of_phantom mapping_impl_lista))
                   | (Some (cnt, s), EInt i) ->
                     (true,
                       updateb
                         ((ccompare_list ccompare_event_data),
                           (equal_list equal_event_data))
                         g (plus_nata cnt one_nata, Z.add s i) m)
                   | (Some (_, _), EFloat _) ->
                     (false,
                       mapping_empty (ccompare_list ccompare_event_data)
                         (of_phantom mapping_impl_lista))
                   | (Some (_, _), EString _) ->
                     (false,
                       mapping_empty (ccompare_list ccompare_event_data)
                         (of_phantom mapping_impl_lista))))
      else (v, m));;

let rec dinsert_cnt
  args t (v, m) =
    (if v then (v, (let g = drop (dgg_k args) t in
                     (match edl_lookup_nat m g
                       with None -> edl_update_nat g one_nata m
                       | Some i -> edl_update_nat g (plus_nata i one_nata) m)))
      else (v, m));;

let rec dinsert_maggaux
  args x aux =
    (let xs = unbox edl_csorted_list_of_set_v x in
      (match aux
        with DCntAux m ->
          (let (v, ma) = fold (dinsert_cnt args) xs (true, m) in
            (v, DCntAux ma))
        | DSumAux m ->
          (let (v, ma) = fold (dinsert_sum args) xs (true, m) in
            (v, DSumAux ma))
        | DRankAux (m, ty) ->
          (let (v, ma) = fold (dinsert_rank args ty) xs (true, m) in
            (v, DRankAux (ma, ty)))));;

let rec dinsert_maggauxa
  args x xa2 = match args, x, xa2 with args, x, None -> None
    | args, x, Some aux ->
        (match dinsert_maggaux args x aux with (true, auxa) -> Some auxa
          | (false, _) -> None);;

let rec gmsaux_in
  x = (fun (_, (_, (_, (_, (_, (table_in, (_, (_, (_, _))))))))) -> table_in)
        x;;

let rec daadd_new_table_msaux
  args ag x sa =
    (let (s, a) = sa in
      (de_gadd_new_table_msaux args x s,
        (if memL (args_ivl args) zero_nata
          then dinsert_maggauxa ag (edl_minus x (gmsaux_in s)) a else a)));;

let rec hm_look_list
  eq h x xa3 = match eq, h, x, xa3 with eq, h, x, [] -> None
    | eq, h, x, y :: ys ->
        (if Z.equal h (fst y) && eq x (fst (snd y)) then Some (snd (snd y))
          else hm_look_list eq h x ys);;

let rec hm_del_list
  eq h x xa3 = match eq, h, x, xa3 with eq, h, x, [] -> []
    | eq, h, x, y :: ys ->
        (if Z.equal h (fst y) && eq x (fst (snd y)) then ys
          else y :: hm_del_list eq h x ys);;

let rec im_fold_idx _A _B
  f a i n acc =
    (if Z.leq n i then (fun () -> acc)
      else binda ((fun () -> Array.get a (Z.to_int i)))
             (fun b ->
               im_fold_idx _A _B f a (Z.add i (Z.of_int 1)) n (f b acc)));;

let rec im_entries _A _B
  q = (let (n, (_, a)) = q in
        im_fold_idx _A _B (fun aa b -> aa @ b) a Z.zero n []);;

let rec im_fill _A _B
  q kvs =
    (match kvs with [] -> (fun () -> q)
      | e :: r ->
        (let (n, (c, a)) = q in
         let i = (fun h n -> Z.logand h (Z.pred n)) (fst e) n in
          binda ((fun () -> Array.get a (Z.to_int i)))
            (fun b ->
              binda ((fun () -> Array.set a (Z.to_int i) (e :: b)))
                (fun _ -> im_fill _A _B (n, (Z.add c (Z.of_int 1), a)) r))));;

let rec im_cap_aux
  k c n =
    (if equal_nata k zero_nata then c
      else (if Z.leq n c then c
             else im_cap_aux (minus_nata k one_nata) (Z.mul (Z.of_int 2) c)
                    n));;

let rec im_cap n = im_cap_aux (nat_of_integer (Z.of_int 64)) (Z.of_int 8) n;;

let rec im_new _A _B
  n = (let m = im_cap n in
        binda ((fun () -> Array.make (Z.to_int m) []))
          (fun a -> (fun () -> (m, (Z.zero, a)))));;

let rec im_grow _A _B
  q = (let (n, (_, _)) = q in
        binda (im_entries _A _B q)
          (fun kvs ->
            binda (im_new _A _B (Z.mul (Z.of_int 2) n))
              (fun qa -> im_fill _A _B qa kvs)));;

let rec im_update_h _A _B
  eq q h x v =
    (let (n, (c, a)) = q in
     let i = (fun h n -> Z.logand h (Z.pred n)) h n in
      binda ((fun () -> Array.get a (Z.to_int i)))
        (fun b ->
          (match hm_look_list eq h x b
            with None ->
              binda ((fun () -> Array.set a (Z.to_int i) ((h, (x, v)) :: b)))
                (fun _ ->
                  (if Z.lt (Z.add c (Z.of_int 1)) n
                    then (fun () -> (n, (Z.add c (Z.of_int 1), a)))
                    else im_grow _A _B (n, (Z.add c (Z.of_int 1), a))))
            | Some _ ->
              binda ((fun () -> Array.set a (Z.to_int i)
                      ((h, (x, v)) :: hm_del_list eq h x b)))
                (fun _ -> (fun () -> q)))));;

let rec im_lookup_h _A _B
  eq q h x =
    (let (n, (_, a)) = q in
      binda ((fun () -> Array.get a (Z.to_int
              ((fun h n -> Z.logand h (Z.pred n)) h n))))
        (fun b -> (fun () -> (hm_look_list eq h x b))));;

let rec hsd_since_loop2
  hsh eq t xs h =
    (match xs with [] -> (fun () -> h)
      | x :: r ->
        (let hx = hsh x in
          binda (im_lookup_h (heap_list heap_event_data) heap_nat eq h hx x)
            (fun v ->
              binda (if is_none v
                      then im_update_h (heap_list heap_event_data) heap_nat eq h
                             hx x t
                      else (fun () -> h))
                (hsd_since_loop2 hsh eq t r))));;

let rec im_update _A _B hsh eq q x v = im_update_h _A _B eq q (hsh x) x v;;

let rec hsd_ins_loop2
  hsh eq t xs h =
    (match xs with [] -> (fun () -> h)
      | x :: r ->
        binda (im_update (heap_list heap_event_data) heap_nat hsh eq h x t)
          (hsd_ins_loop2 hsh eq t r));;

let rec hsd_add_new_table2
  hsh eq args x q =
    (let ((t, (gc, (mL, (mR, (dp, (di, tin)))))), (hin, hsince)) = q in
     let xs = unbox edl_csorted_list_of_set_v x in
      binda (hsd_since_loop2 hsh eq t xs hsince)
        (fun hsincea ->
          (if memL (args_ivl args) zero_nata
            then binda (hsd_ins_loop2 hsh eq t xs hin)
                   (fun hina ->
                     (fun () ->
                       ((t, (gc, (mL, (mR,
(dp, (append_queue (t, x) di, edl_union tin x)))))),
                         (hina, hsincea))))
            else (fun () ->
                   ((t, (gc, (mL, (mR, (append_queue (t, x) dp, (di, tin)))))),
                     (hin, hsincea))))));;

let rec add_new_table_d
  args x xa2 = match args, x, xa2 with
    args, x, MSD_imp q ->
      binda (hsd_add_new_table2
              (fun t -> let rec go h l = (match l with [] -> h | EInt z :: r -> go (h * 31 + Z.hash z) r | EFloat f :: r -> go (h * 31 + Hashtbl.hash f) r | EString s :: r -> go (h * 31 + Hashtbl.hash s) r) in Z.of_int ((go 17 t) land 1073741823))
              ueq args x q)
        (fun qa -> (fun () -> (MSD_imp qa)))
    | args, x, MSD_dns s ->
        (fun () -> (MSD_dns (de_gadd_new_table_msaux args x s)))
    | args, x, MSD_evt a ->
        (fun () -> (MSD_evt (de_gadd_new_table_sevt args x a)))
    | args, x, MSD_agg (ag, s) ->
        (fun () -> (MSD_agg (ag, daadd_new_table_msaux args ag x s)));;

let rec de_gvalid_tuple
  tuple_since =
    (fun (t, asa) ->
      (match edl_lookup_nat tuple_since asa with None -> false
        | Some ta -> less_eq_nat ta t));;

let rec upd_set_keys (_C1, _C2, _C3, _C4)
  z (t, x) (m, y) =
    (upd_set (_C1, _C2, _C3, _C4) m (fun _ -> t) (z x t),
      sup_seta (_C2, _C3) y (z x t));;

let rec de_gadd_new_ts_msauxa
  args nt
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (let i = args_ivl args in
       let (data_preva, move) =
         takedropWhile_queue (fun (ta, _) -> memL i (minus_nata nt ta))
           data_prev
         in
       let data_ina = fold (fun (ta, x) -> append_queue (ta, x)) move data_in in
       let (tuple_ina, add) =
         fold (upd_set_keys
                (finite_UNIV_list, (ceq_list ceq_event_data),
                  (ccompare_list ccompare_event_data),
                  (equal_list equal_event_data))
                (fun x ta ->
                  edl_filter (fun asa -> de_gvalid_tuple tuple_since (ta, asa))
                    x))
           move (tuple_in, edl_bot)
         in
        (nt, (gc, (msk, (data_preva,
                          (data_ina,
                            (edl_union table_in add,
                              (de_gidx_upd args
                                 (fun _ ->
                                   didx_union
                                     (ceq_event_data, ccompare_event_data)
                                     idx_in
                                     (didx (ceq_event_data, ccompare_event_data)
                                       msk add)),
                                (tuple_ina, (idx_since, tuple_since))))))))));;

let rec filter_cfi _B (_A1, _A2, _A3, _A4)
  xa = Abs_comp_fun_idem
         (fun a (m, y) ->
           (match lookupa (_A2, _A3) m a with None -> (m, y)
             | Some u ->
               (if eq _B xa u
                 then (delete (_A2, _A3) a m,
                        sup_seta (_A1, _A2) y
                          (insert (_A1, _A2) a (bot_set (_A1, _A2, _A4))))
                 else (m, y))));;

let rec filter_set _A (_B1, _B2, _B3, _B4, _B5)
  (t, a) (m, y) =
    (if finite (_B1, _B2, _B3) a
      then set_fold_cfi (_B2, _B3) (filter_cfi _A (_B2, _B3, _B4, _B5) t) (m, y)
             a
      else failwith "upd_set: infinite"
             (fun _ -> filter_set _A (_B1, _B2, _B3, _B4, _B5) (t, a) (m, y)));;

let rec minus_comp
  comp t1 t2 =
    (if small_rbta t2 then folda (fun k _ -> rbt_comp_delete comp k) t2 t1
      else (if small_rbta t1
             then rbtreeify
                    (filtera (fun (k, _) -> is_none (rbt_comp_lookup comp t2 k))
                      (entries t1))
             else (match t2 with Empty -> t1
                    | Branch (_, l2, a, (), r2) ->
                      (let (l1, (_, r1)) = split_comp comp t1 a in
                        rbt_join2a (minus_comp comp l1 l2)
                          (minus_comp comp r1 r2)))));;

let rec rbt_minus_rbt_join2 _A
  xb xc =
    Mapping_RBTa
      (rbt_recolor
        (minus_comp (the (ccompare _A)) (impl_ofa _A xb) (impl_ofa _A xc)));;

let rec minus_set (_A1, _A2)
  a b = match a, b with
    RBT_set t1, RBT_set t2 ->
      (match ccompare _A2
        with None ->
          failwith "minus RBT_set RBT_set: ccompare = None"
            (fun _ -> minus_set (_A1, _A2) (RBT_set t1) (RBT_set t2))
        | Some _ -> RBT_set (rbt_minus_rbt_join2 _A2 t1 t2))
    | a, b -> inf_seta (_A1, _A2) a (uminus_set b);;

let rec dbucket (_A1, _A2, _A3)
  d k = (match lookupa ((ccompare_list _A2), (equal_list _A3)) d k
          with None ->
            set_empty ((ceq_list _A1), (ccompare_list _A2))
              (of_phantom set_impl_lista)
          | Some z -> z);;

let rec didx_minus (_A1, _A2, _A3)
  i d = filterc (ccompare_list _A2)
          (fun _ y ->
            not (is_empty
                  (card_UNIV_list, (ceq_list _A1), (cproper_interval_list _A2))
                  y))
          (map_values (ccompare_list _A2)
            (fun k y ->
              minus_set ((ceq_list _A1), (ccompare_list _A2)) y
                (dbucket (_A1, _A2, _A3) d k))
            i);;

let rec de_gshift_end
  args nt
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (let i = args_ivl args in
       let data_preva =
         dropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta)))
           data_prev
         in
       let (data_ina, discard) =
         takedropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta)))
           data_in
         in
       let (tuple_ina, del) =
         fold (filter_set equal_nat
                (finite_UNIV_list, (ceq_list ceq_event_data),
                  (ccompare_list ccompare_event_data),
                  (equal_list equal_event_data), set_impl_list))
           discard (tuple_in, edl_bot)
         in
        (t, (gc, (msk, (data_preva,
                         (data_ina,
                           (edl_minus table_in del,
                             (de_gidx_upd args
                                (fun _ ->
                                  didx_minus
                                    (ceq_event_data, ccompare_event_data,
                                      equal_event_data)
                                    idx_in
                                    (didx (ceq_event_data, ccompare_event_data)
                                      msk del)),
                               (tuple_ina, (idx_since, tuple_since))))))))));;

let rec de_gadd_new_ts_msaux
  args nt daux = de_gadd_new_ts_msauxa args nt (de_gshift_end args nt daux);;

let rec edl_rbtc_del
  x xa1 = match x, xa1 with x, Empty -> Empty
    | x, Branch (cc, a, y, s, b) ->
        (match edl_comparator x y with Eqa -> combinea a b
          | Lt -> edl_rbtc_del_from_left x a y s b
          | Gt -> edl_rbtc_del_from_right x a y s b)
and edl_rbtc_del_from_left
  x xa1 y s b = match x, xa1, y, s, b with
    x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (edl_rbtc_del x (Branch (B, lt, z, v, rt))) y s b
    | x, Empty, y, s, b -> Branch (R, edl_rbtc_del x Empty, y, s, b)
    | x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, edl_rbtc_del x (Branch (R, va, vb, vc, vd)), y, s, b)
and edl_rbtc_del_from_right
  x a y s xa4 = match x, a, y, s, xa4 with
    x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (edl_rbtc_del x (Branch (B, lt, z, v, rt)))
    | x, a, y, s, Empty -> Branch (R, a, y, s, edl_rbtc_del x Empty)
    | x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, edl_rbtc_del x (Branch (R, va, vb, vc, vd)));;

let rec edl_rbtc_delete k t = paint B (edl_rbtc_del k t);;

let rec edl_rbt_delete_nat
  xb xc = Mapping_RBTa (edl_rbtc_delete xb (unbox edl_impl_of_nat_v xc));;

let rec edl_delete_nat
  k x1 = match k, x1 with
    k, RBT_Mapping t -> RBT_Mapping (edl_rbt_delete_nat k t)
    | k, Assoc_List_Mapping al ->
        Assoc_List_Mapping (deletea (equal_list equal_event_data) k al)
    | k, Mapping m -> Mapping (fun_upd (equal_list equal_event_data) m k None);;

let rec de_gevt_del
  t cc =
    fold (fun ta (c, s) ->
           (match edl_lookup_nat c ta with None -> (c, s)
             | Some k ->
               (if less_eq_nat k one_nata
                 then (edl_delete_nat ta c, unbox edl_remove_v ta s)
                 else (edl_update_nat ta (minus_nata k one_nata) c, s))))
      (unbox edl_csorted_list_of_set_v t) cc;;

let rec de_gsevt_expire
  args nt win cnt cur =
    (match safe_hd win with (None, wina) -> (wina, (cnt, cur))
      | (Some e, wina) ->
        (if memR (args_ivl args) (minus_nata nt (fst e)) then (wina, (cnt, cur))
          else (let (a, b) = de_gevt_del (snd e) (cnt, cur) in
                 de_gsevt_expire args nt (tl_queue wina) a b)));;

let rec de_gsevt_move
  args nt pend win cnt cur =
    (match safe_hd pend with (None, penda) -> (penda, (win, (cnt, cur)))
      | (Some e, penda) ->
        (if memL (args_ivl args) (minus_nata nt (fst e))
          then (if memR (args_ivl args) (minus_nata nt (fst e))
                 then (let (a, b) = de_gevt_add (snd e) (cnt, cur) in
                        de_gsevt_move args nt (tl_queue penda)
                          (append_queue e win) a b)
                 else de_gsevt_move args nt (tl_queue penda) win cnt cur)
          else (penda, (win, (cnt, cur)))));;

let rec de_gadd_new_ts_sevt
  args nt aux =
    (let (_, (pend, (win, (cnt, cur)))) = aux in
     let (penda, (wina, (cnta, cura))) = de_gsevt_move args nt pend win cnt cur
       in
     let (winb, (cntb, curb)) = de_gsevt_expire args nt wina cnta cura in
      (nt, (penda, (winb, (cntb, curb)))));;

let rec gvalid_tuple (_A1, _A2)
  tuple_since =
    (fun (t, asa) ->
      (match lookupa ((ccompare_list _A1), (equal_list _A2)) tuple_since asa
        with None -> false | Some ta -> less_eq_nat ta t));;

let rec gidx_upd _A
  args w =
    (if didx_live args then w ()
      else mapping_empty (ccompare_list _A) (of_phantom mapping_impl_lista));;

let rec gadd_new_ts_msaux_add (_A1, _A2, _A3)
  args nt
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (let i = args_ivl args in
       let (data_preva, move) =
         takedropWhile_queue (fun (ta, _) -> memL i (minus_nata nt ta))
           data_prev
         in
       let data_ina = fold (fun (ta, x) -> append_queue (ta, x)) move data_in in
       let (tuple_ina, add) =
         fold (upd_set_keys
                (finite_UNIV_list, (ceq_list _A1), (ccompare_list _A2),
                  (equal_list _A3))
                (fun x ta ->
                  filter ((ceq_list _A1), (ccompare_list _A2))
                    (fun asa -> gvalid_tuple (_A2, _A3) tuple_since (ta, asa))
                    x))
           move
           (tuple_in,
             set_empty ((ceq_list _A1), (ccompare_list _A2))
               (of_phantom set_impl_lista))
         in
        ((nt, (gc, (msk, (data_preva,
                           (data_ina,
                             (sup_seta ((ceq_list _A1), (ccompare_list _A2))
                                table_in add,
                               (gidx_upd _A2 args
                                  (fun _ ->
                                    didx_union (_A1, _A2) idx_in
                                      (didx (_A1, _A2) msk add)),
                                 (tuple_ina, (idx_since, tuple_since))))))))),
          filter ((ceq_list _A1), (ccompare_list _A2))
            (fun k ->
              is_none
                (lookupa ((ccompare_list _A2), (equal_list _A3)) tuple_in k))
            add));;

let rec equal_tree _A
  x0 x1 = match x0, x1 with Leaf, Node (x21, x22, x23) -> false
    | Node (x21, x22, x23), Leaf -> false
    | Node (x21, x22, x23), Node (y21, y22, y23) ->
        equal_tree _A x21 y21 && (eq _A x22 y22 && equal_tree _A x23 y23)
    | Leaf, Leaf -> true;;

let rec equal_wf_wbt (_A1, _A2)
  xa xc =
    equal_tree (equal_prod _A1 equal_nat) (rep_wf_wbt _A2 xa)
      (rep_wf_wbt _A2 xc);;

let rec tree_inorder _A xa = inorder (rep_wf_wbt _A xa);;

let rec equal_treelist (_A1, _A2)
  (Collapse y1) (Collapse y2) =
    (if equal_wf_wbt (_A1, _A2) y2 (empty_tree _A2)
      then equal_wf_wbt (_A1, _A2) y1 (empty_tree _A2)
      else equal_lista _A1 (tree_inorder _A2 y1) (tree_inorder _A2 y2));;

let rec split_mina _A
  (Node (l, (a, uu), r)) =
    (if equal_tree (equal_prod _A equal_nat) l Leaf then (a, r)
      else (let (x, la) = split_mina _A l in (x, balanceL la a r)));;

let rec del_max _A
  (Node (l, (a, uu), r)) =
    (if equal_tree (equal_prod _A equal_nat) r Leaf then (a, l)
      else (let (x, ra) = del_max _A r in (x, balanceR l a ra)));;

let rec size_tree
  = function Leaf -> zero_nata
    | Node (x21, x22, x23) ->
        plus_nata (plus_nata (size_tree x21) (size_tree x23)) (suc zero_nata);;

let rec combineb _A
  x0 x1 = match x0, x1 with Leaf, Leaf -> Leaf
    | Leaf, Node (v, va, vb) -> Node (v, va, vb)
    | Node (v, va, vb), Leaf -> Node (v, va, vb)
    | Node (v, va, vb), Node (vc, vd, ve) ->
        (if less_nat (size_tree (Node (vc, vd, ve)))
              (size_tree (Node (v, va, vb)))
          then (let (lMax, l) = del_max _A (Node (v, va, vb)) in
                 balanceL l lMax (Node (vc, vd, ve)))
          else (let (a, b) = split_mina _A (Node (vc, vd, ve)) in
                 balanceR (Node (v, va, vb)) a b));;

let rec deletec (_A1, _A2)
  uu x1 = match uu, x1 with uu, Leaf -> Leaf
    | x, Node (l, (a, uv), r) ->
        (match cmp (_A1, _A2) x a
          with LT -> balanceL (deletec (_A1, _A2) x l) a r
          | EQ -> combineb _A1 l r
          | GT -> balanceR l a (deletec (_A1, _A2) x r));;

let rec tree_remove (_A1, _A2)
  xb xc = Abs_wf_wbt (deletec (_A1, _A2) xb (rep_wf_wbt _A2 xc));;

let rec remove_treelist (_A1, _A2)
  x (Collapse y) = Collapse (tree_remove (_A1, _A2) x y);;

let rec ddelete_rank
  args ty t (v, m) =
    (if v then (let g = drop (dgg_k args) t in
                let e = umeval_trm (dgg_trm args) t in
                let (a, b) =
                  (match
                    (lookupa
                       ((ccompare_list ccompare_event_data),
                         (equal_list equal_event_data))
                       m g,
                      (e, ty))
                    with (None, (EInt _, IntT)) -> (true, m)
                    | (None, (EInt _, StringT)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (None, (EFloat _, _)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (None, (EString _, IntT)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (None, (EString _, StringT)) -> (true, m)
                    | (Some (LInt s), (EInt c, IntT)) ->
                      (true,
                        (let l =
                           remove_treelist (equal_integer, linorder_integer) c s
                           in
                          (if equal_treelist (equal_integer, linorder_integer) l
                                (empty_treelist linorder_integer)
                            then delete
                                   ((ccompare_list ccompare_event_data),
                                     (equal_list equal_event_data))
                                   g m
                            else updateb
                                   ((ccompare_list ccompare_event_data),
                                     (equal_list equal_event_data))
                                   g (LInt l) m)))
                    | (Some (LInt _), (EInt _, StringT)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (Some (LInt _), (EFloat _, _)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (Some (LInt _), (EString _, _)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (Some (LString _), (EInt _, _)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (Some (LString _), (EFloat _, _)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (Some (LString _), (EString _, IntT)) ->
                      (false,
                        mapping_empty (ccompare_list ccompare_event_data)
                          (of_phantom mapping_impl_lista))
                    | (Some (LString s), (EString c, StringT)) ->
                      (true,
                        (let l =
                           remove_treelist (equal_string8, linorder_string8) c s
                           in
                          (if equal_treelist (equal_string8, linorder_string8) l
                                (empty_treelist linorder_string8)
                            then delete
                                   ((ccompare_list ccompare_event_data),
                                     (equal_list equal_event_data))
                                   g m
                            else updateb
                                   ((ccompare_list ccompare_event_data),
                                     (equal_list equal_event_data))
                                   g (LString l) m))))
                  in
                 (a, b))
      else (v, m));;

let rec ddelete_sum
  args t (v, m) =
    (if v then (let g = drop (dgg_k args) t in
                let e = umeval_trm (dgg_trm args) t in
                 (match
                   (lookupa
                      ((ccompare_list ccompare_event_data),
                        (equal_list equal_event_data))
                      m g,
                     e)
                   with (None, _) ->
                     (false,
                       mapping_empty (ccompare_list ccompare_event_data)
                         (of_phantom mapping_impl_lista))
                   | (Some (cnt, s), EInt i) ->
                     (true,
                       (if equal_nata cnt one_nata
                         then delete
                                ((ccompare_list ccompare_event_data),
                                  (equal_list equal_event_data))
                                g m
                         else updateb
                                ((ccompare_list ccompare_event_data),
                                  (equal_list equal_event_data))
                                g (minus_nata cnt one_nata, Z.sub s i) m))
                   | (Some (_, _), EFloat _) ->
                     (false,
                       mapping_empty (ccompare_list ccompare_event_data)
                         (of_phantom mapping_impl_lista))
                   | (Some (_, _), EString _) ->
                     (false,
                       mapping_empty (ccompare_list ccompare_event_data)
                         (of_phantom mapping_impl_lista))))
      else (v, m));;

let rec ddelete_cnt
  args t (v, m) =
    (if v then (v, (let g = drop (dgg_k args) t in
                     (match edl_lookup_nat m g with None -> m
                       | Some i ->
                         (if equal_nata i one_nata then edl_delete_nat g m
                           else edl_update_nat g (minus_nata i one_nata) m))))
      else (v, m));;

let rec ddelete_maggaux
  args x aux =
    (let xs = unbox edl_csorted_list_of_set_v x in
      (match aux
        with DCntAux m ->
          (let (v, ma) = fold (ddelete_cnt args) xs (true, m) in
            (v, DCntAux ma))
        | DSumAux m ->
          (let (v, ma) = fold (ddelete_sum args) xs (true, m) in
            (v, DSumAux ma))
        | DRankAux (m, ty) ->
          (let (v, ma) = fold (ddelete_rank args ty) xs (true, m) in
            (v, DRankAux (ma, ty)))));;

let rec ddelete_maggauxa
  args x xa2 = match args, x, xa2 with args, x, None -> None
    | args, x, Some aux ->
        (match ddelete_maggaux args x aux with (true, auxa) -> Some auxa
          | (false, _) -> None);;

let rec gshift_end_del (_A1, _A2, _A3)
  args nt
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (let i = args_ivl args in
       let data_preva =
         dropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta)))
           data_prev
         in
       let (data_ina, discard) =
         takedropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta)))
           data_in
         in
       let (tuple_ina, del) =
         fold (filter_set equal_nat
                (finite_UNIV_list, (ceq_list _A1), (ccompare_list _A2),
                  (equal_list _A3), set_impl_list))
           discard
           (tuple_in,
             set_empty ((ceq_list _A1), (ccompare_list _A2))
               (of_phantom set_impl_lista))
         in
        ((t, (gc, (msk, (data_preva,
                          (data_ina,
                            (minus_set ((ceq_list _A1), (ccompare_list _A2))
                               table_in del,
                              (gidx_upd _A2 args
                                 (fun _ ->
                                   didx_minus (_A1, _A2, _A3) idx_in
                                     (didx (_A1, _A2) msk del)),
                                (tuple_ina, (idx_since, tuple_since))))))))),
          del));;

let rec daadd_new_ts_msaux
  args ag nt sa =
    (let (s, a) = sa in
     let (s1, del) =
       gshift_end_del (ceq_event_data, ccompare_event_data, equal_event_data)
         args nt s
       in
     let (s2, add) =
       gadd_new_ts_msaux_add
         (ceq_event_data, ccompare_event_data, equal_event_data) args nt s1
       in
      (s2, dinsert_maggauxa ag add (ddelete_maggauxa ag del a)));;

let rec hsd_upd_loop2
  hsh eq t xs hs h y =
    (match xs with [] -> (fun () -> (h, y))
      | x :: r ->
        (let hx = hsh x in
          binda (im_lookup_h (heap_list heap_event_data) heap_nat eq hs hx x)
            (fun a ->
              (match a with None -> hsd_upd_loop2 hsh eq t r hs h y
                | Some ta ->
                  (if less_eq_nat ta t
                    then binda (im_update_h (heap_list heap_event_data) heap_nat
                                 eq h hx x t)
                           (fun ha ->
                             hsd_upd_loop2 hsh eq t r hs ha (edl_insert x y))
                    else hsd_upd_loop2 hsh eq t r hs h y)))));;

let rec hsd_move_loop2
  hsh eq xs hs h y =
    (match xs with [] -> (fun () -> (h, y))
      | tX :: r ->
        binda (hsd_upd_loop2 hsh eq (fst tX)
                (unbox edl_csorted_list_of_set_v (snd tX)) hs h y)
          (fun p -> hsd_move_loop2 hsh eq r hs (fst p) (snd p)));;

let rec hsd_add_new_ts2a
  hsh eq args nt q =
    (let ((_, (gc, (mL, (mR, (dp, (di, tin)))))), (hin, hsince)) = q in
     let i = args_ivl args in
     let p = takedropWhile_queue (fun (t, _) -> memL i (minus_nata nt t)) dp in
     let dia = fold append_queue (snd p) di in
      binda (hsd_move_loop2 hsh eq (snd p) hsince hin edl_bot)
        (fun r ->
          (fun () ->
            ((nt, (gc, (mL, (mR, (fst p, (dia, edl_union tin (snd r))))))),
              (fst r, hsince)))));;

let rec im_delete_h _A _B
  eq q h x =
    (let (n, (c, a)) = q in
     let i = (fun h n -> Z.logand h (Z.pred n)) h n in
      binda ((fun () -> Array.get a (Z.to_int i)))
        (fun b ->
          (match hm_look_list eq h x b with None -> (fun () -> q)
            | Some _ ->
              binda ((fun () -> Array.set a (Z.to_int i)
                      (hm_del_list eq h x b)))
                (fun _ -> (fun () -> (n, (Z.sub c (Z.of_int 1), a)))))));;

let rec hsd_filter_loop2
  hsh eq t xs h y =
    (match xs with [] -> (fun () -> (h, y))
      | x :: r ->
        (let hx = hsh x in
          binda (im_lookup_h (heap_list heap_event_data) heap_nat eq h hx x)
            (fun v ->
              (if equal_optiona equal_nat v (Some t)
                then binda (im_delete_h (heap_list heap_event_data) heap_nat eq
                             h hx x)
                       (fun ha ->
                         hsd_filter_loop2 hsh eq t r ha (edl_insert x y))
                else hsd_filter_loop2 hsh eq t r h y))));;

let rec hsd_expire_loop2
  hsh eq xs h y =
    (match xs with [] -> (fun () -> (h, y))
      | tX :: r ->
        binda (hsd_filter_loop2 hsh eq (fst tX)
                (unbox edl_csorted_list_of_set_v (snd tX)) h y)
          (fun p -> hsd_expire_loop2 hsh eq r (fst p) (snd p)));;

let rec hsd_shift_end2
  hsh eq args nt q =
    (let ((t, (gc, (mL, (mR, (dp, (di, tin)))))), (hin, hsince)) = q in
     let i = args_ivl args in
     let dpa =
       dropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta))) dp in
     let p =
       takedropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta))) di
       in
      binda (hsd_expire_loop2 hsh eq (snd p) hin edl_bot)
        (fun r ->
          (fun () ->
            ((t, (gc, (mL, (mR, (dpa, (fst p, edl_minus tin (snd r))))))),
              (fst r, hsince)))));;

let rec hsd_add_new_ts2
  hsh eq args nt q =
    binda (hsd_shift_end2 hsh eq args nt q) (hsd_add_new_ts2a hsh eq args nt);;

let rec add_new_ts_d
  args nt x2 = match args, nt, x2 with
    args, nt, MSD_imp q ->
      binda (hsd_add_new_ts2
              (fun t -> let rec go h l = (match l with [] -> h | EInt z :: r -> go (h * 31 + Z.hash z) r | EFloat f :: r -> go (h * 31 + Hashtbl.hash f) r | EString s :: r -> go (h * 31 + Hashtbl.hash s) r) in Z.of_int ((go 17 t) land 1073741823))
              ueq args nt q)
        (fun qa -> (fun () -> (MSD_imp qa)))
    | args, nt, MSD_dns s ->
        (fun () -> (MSD_dns (de_gadd_new_ts_msaux args nt s)))
    | args, nt, MSD_evt a ->
        (fun () -> (MSD_evt (de_gadd_new_ts_sevt args nt a)))
    | args, nt, MSD_agg (ag, s) ->
        (fun () -> (MSD_agg (ag, daadd_new_ts_msaux args ag nt s)));;

let rec de_gresult_msaux
  args (nt, (gc, (msk, (data_prev,
                         (data_in,
                           (table_in,
                             (idx_in,
                               (tuple_in, (idx_since, tuple_since)))))))))
    = table_in;;

let rec de_gresult_sevt args aux = (let (_, (_, (_, (_, cur)))) = aux in cur);;

let rec double_of_event_data_agg = function EInt x -> Z.to_float x
                                   | EFloat x -> x
                                   | EString uu -> failwith "undefined";;

let rec integer_of_int (Int_of_integer k) = k;;

let edl_keys_nat_v :
  (((event_data list), nat) mapping -> (event_data list) set) boxed
  = Box (keys (cenum_list, (ceq_list ceq_event_data),
                (ccompare_list ccompare_event_data), set_impl_list));;

let rec select
  x0 n = match x0, n with
    Node (l, (a, uu), r), n ->
      (let s = size_wbt l in
        (match cmp (equal_nat, linorder_nat) s n
          with LT -> select r (minus_nata (minus_nata n s) one_nata) | EQ -> a
          | GT -> select l n))
    | Leaf, n -> nth [] n;;

let rec tree_select _A xa = select (rep_wf_wbt _A xa);;

let rec get_treelist _A (Collapse y) n = tree_select _A y n;;

let rec get_edata_list
  x0 n = match x0, n with
    LString l, n -> EString (get_treelist linorder_string8 l n)
    | LInt l, n -> EInt (get_treelist linorder_integer l n);;

let rec dgg_op
  (Daggargs_ext (dgg_g0, dgg_op, dgg_trm, dgg_k, dgg_p, more)) = dgg_op;;

let rec dgg_g0
  (Daggargs_ext (dgg_g0, dgg_op, dgg_trm, dgg_k, dgg_p, more)) = dgg_g0;;

let rec dgg_p
  (Daggargs_ext (dgg_g0, dgg_op, dgg_trm, dgg_k, dgg_p, more)) = dgg_p;;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let rec double_of_int (Int_of_integer x) = Z.to_float x;;

let rec tree_size _A xa = size_wbt (rep_wf_wbt _A xa);;

let rec length_treelist _A (Collapse y) = tree_size _A y;;

let rec get_length
  l = (match l with LInt a -> length_treelist linorder_integer a
        | LString a -> length_treelist linorder_string8 a);;

let rec dmap_result
  p f m =
    edl_image
      (fun g ->
        (match
          lookupa
            ((ccompare_list ccompare_event_data), (equal_list equal_event_data))
            m g
          with None -> g | Some i -> take p g @ f i :: drop p g))
      (keys (cenum_list, (ceq_list ceq_event_data),
              (ccompare_list ccompare_event_data), set_impl_list)
        m);;

let rec dvd (_A1, _A2)
  a b = eq _A1
          (modulo
            _A2.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo
            b a)
          (zero _A2.algebraic_semidom_semidom_modulo.semidom_divide_algebraic_semidom.semidom_semidom_divide.comm_semiring_1_cancel_semidom.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec aggreg_default_value
  op t =
    (match (op, t) with (Agg_Cnt, TInt) -> EInt Z.zero
      | (Agg_Cnt, TFloat) -> EFloat 0.0 | (Agg_Cnt, TString) -> EString ""
      | (Agg_Min, TInt) -> EInt Z.zero
      | (Agg_Min, TFloat) -> EFloat Stdlib.infinity
      | (Agg_Min, TString) -> EString "" | (Agg_Max, TInt) -> EInt Z.zero
      | (Agg_Max, TFloat) -> EFloat (Stdlib.(~-.) Stdlib.infinity)
      | (Agg_Max, TString) -> EString "" | (Agg_Sum, TInt) -> EInt Z.zero
      | (Agg_Sum, TFloat) -> EFloat 0.0 | (Agg_Sum, TString) -> EString ""
      | (Agg_Avg, TInt) -> EInt Z.zero | (Agg_Avg, TFloat) -> EFloat 0.0
      | (Agg_Avg, TString) -> EString "" | (Agg_Med, TInt) -> EInt Z.zero
      | (Agg_Med, TFloat) -> EFloat 0.0 | (Agg_Med, TString) -> EString "");;

let rec the_enat (Enat n) = n;;

let rec flatten_multiset
  m = maps (fun (x, c) -> replicate (the_enat c) x)
        (csorted_list_of_set
          ((ceq_prod ceq_event_data ceq_enat),
            (ccompare_prod ccompare_event_data ccompare_enat))
          m);;

let rec finite_multiset_insert_fun
  (uu, k) v = (if equal_enat k Infinity_enat then false else true) && v;;

let finite_multiset_cfi : ((event_data * enat), bool) comp_fun_idem
  = Abs_comp_fun_idem finite_multiset_insert_fun;;

let rec finite_multiset
  m = (if finite
            ((finite_UNIV_prod finite_UNIV_event_data finite_UNIV_enat),
              (ceq_prod ceq_event_data ceq_enat),
              (ccompare_prod ccompare_event_data ccompare_enat))
            m
        then set_fold_cfi
               ((ceq_prod ceq_event_data ceq_enat),
                 (ccompare_prod ccompare_event_data ccompare_enat))
               finite_multiset_cfi true m
        else false);;

let rec eval_agg_op
  x0 m = match x0, m with
    (Agg_Cnt, ty), m ->
      (let y0 = aggreg_default_value Agg_Cnt ty in
        (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
          | ([], false) -> y0
          | (a :: lista, true) ->
            EInt (integer_of_int (int_of_nat (size_lista (a :: lista))))
          | (_ :: _, false) -> y0))
    | (Agg_Min, ty), m ->
        (let y0 = aggreg_default_value Agg_Min ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) -> foldl (min ord_event_data) a lista
            | (_ :: _, false) -> y0))
    | (Agg_Max, ty), m ->
        (let y0 = aggreg_default_value Agg_Max ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) -> foldl (max ord_event_data) a lista
            | (_ :: _, false) -> y0))
    | (Agg_Sum, ty), m ->
        (let y0 = aggreg_default_value Agg_Sum ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) -> foldl plus_event_data a lista
            | (_ :: _, false) -> y0))
    | (Agg_Avg, ty), m ->
        (let y0 = aggreg_default_value Agg_Avg ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) ->
              EFloat
                (Stdlib.(/.)
                  (double_of_event_data_agg (foldl plus_event_data a lista))
                  (double_of_int (int_of_nat (size_lista (a :: lista)))))
            | (_ :: _, false) -> y0))
    | (Agg_Med, ty), m ->
        (let y0 = aggreg_default_value Agg_Med ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) ->
              EFloat
                (let u = size_lista (a :: lista) in
                 let ua = divide_nata u (nat_of_integer (Z.of_int 2)) in
                  (if dvd (equal_nat, semidom_modulo_nat)
                        (nat_of_integer (Z.of_int 2)) u
                    then Stdlib.(/.)
                           (Stdlib.(+.)
                             (double_of_event_data_agg
                               (nth (a :: lista) (minus_nata ua one_nata)))
                             (double_of_event_data_agg (nth (a :: lista) ua)))
                           (double_of_int (Int_of_integer (Z.of_int 2)))
                    else double_of_event_data_agg (nth (a :: lista) ua)))
            | (_ :: _, false) -> y0));;

let rec dresult_maggaux
  args aux =
    (let g0 = dgg_g0 args in
     let omega = dgg_op args in
     let p = dgg_p args in
      (match aux
        with DCntAux m ->
          (if g0 && unbox edl_set_eq_v (unbox edl_keys_nat_v m) edl_bot
            then edl_insert
                   [eval_agg_op omega
                      (set_empty
                        ((ceq_prod ceq_event_data ceq_enat),
                          (ccompare_prod ccompare_event_data ccompare_enat))
                        (of_phantom
                          (set_impl_proda set_impl_event_data set_impl_enat)))]
                   edl_bot
            else dmap_result p (fun k -> EInt (integer_of_int (int_of_nat k)))
                   m)
        | DSumAux m ->
          (if g0 && unbox edl_set_eq_v
                      (keys (cenum_list, (ceq_list ceq_event_data),
                              (ccompare_list ccompare_event_data),
                              set_impl_list)
                        m)
                      edl_bot
            then edl_insert
                   [eval_agg_op omega
                      (set_empty
                        ((ceq_prod ceq_event_data ceq_enat),
                          (ccompare_prod ccompare_event_data ccompare_enat))
                        (of_phantom
                          (set_impl_proda set_impl_event_data set_impl_enat)))]
                   edl_bot
            else (match fst omega
                   with Agg_Sum -> dmap_result p (fun k -> EInt (snd k)) m
                   | Agg_Avg ->
                     dmap_result p
                       (fun k ->
                         EFloat
                           (Stdlib.(/.) (double_of_event_data (EInt (snd k)))
                             (double_of_int (int_of_nat (fst k)))))
                       m))
        | DRankAux (m, _) ->
          (if g0 && unbox edl_set_eq_v
                      (keys (cenum_list, (ceq_list ceq_event_data),
                              (ccompare_list ccompare_event_data),
                              set_impl_list)
                        m)
                      edl_bot
            then edl_insert
                   [eval_agg_op omega
                      (set_empty
                        ((ceq_prod ceq_event_data ceq_enat),
                          (ccompare_prod ccompare_event_data ccompare_enat))
                        (of_phantom
                          (set_impl_proda set_impl_event_data set_impl_enat)))]
                   edl_bot
            else (match fst omega
                   with Agg_Min ->
                     dmap_result p (fun k -> get_edata_list k zero_nata) m
                   | Agg_Max ->
                     dmap_result p
                       (fun k ->
                         get_edata_list k (minus_nata (get_length k) one_nata))
                       m
                   | Agg_Med ->
                     dmap_result p
                       (fun k ->
                         (let u = get_length k in
                          let ua = divide_nata u (nat_of_integer (Z.of_int 2))
                            in
                           EFloat
                             (if dvd (equal_nat, semidom_modulo_nat)
                                   (nat_of_integer (Z.of_int 2)) u
                               then Stdlib.(/.)
                                      (Stdlib.(+.)
(double_of_event_data_agg (get_edata_list k (minus_nata ua one_nata)))
(double_of_event_data_agg (get_edata_list k ua)))
                                      (double_of_int
(Int_of_integer (Z.of_int 2)))
                               else double_of_event_data_agg
                                      (get_edata_list k ua))))
                       m))));;

let edl_impl_of_table_v :
  (((event_data list), (event_data list) set) mapping_rbt ->
    ((event_data list), (event_data list) set) rbt)
    boxed
  = Box (impl_ofa (ccompare_list ccompare_event_data));;

let rec edl_rbt_lookup_table
  t k = edl_rbtc_lookup (unbox edl_impl_of_table_v t) k;;

let rec edl_lookup_table
  = function RBT_Mapping t -> edl_rbt_lookup_table t
    | Assoc_List_Mapping al -> lookup (equal_list equal_event_data) al;;

let edl_keys_table_v :
  (((event_data list), (event_data list) set) mapping -> (event_data list) set)
    boxed
  = Box (keys (cenum_list, (ceq_list ceq_event_data),
                (ccompare_list ccompare_event_data), set_impl_list));;

let edl_cluster_v :
  ((event_data list -> (event_data list) option) ->
    (event_data list) set -> ((event_data list), (event_data list) set) mapping)
    boxed
  = Box (cluster
          ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data),
            set_impl_list)
          (ccompare_list ccompare_event_data));;

let rec uagg_values
  f g = (let vals =
           cluster
             ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data),
               set_impl_list)
             ccompare_event_data (comp (fun a -> Some a) (umeval_trm f)) g
           in
          image (ceq_event_data, ccompare_event_data)
            ((ceq_prod ceq_event_data ceq_enat),
              (ccompare_prod ccompare_event_data ccompare_enat),
              (set_impl_prod set_impl_event_data set_impl_enat))
            (fun v ->
              (let Some s =
                 lookupa (ccompare_event_data, equal_event_data) vals v in
                (v, ecard (card_UNIV_list, (ceq_list ceq_event_data),
                            (ccompare_list ccompare_event_data))
                      s)))
            (keys (cenum_event_data, ceq_event_data, ccompare_event_data,
                    set_impl_event_data)
              vals));;

let rec uagg
  g0 omega f k pos rel =
    (if g0 && unbox edl_is_empty_v rel
      then edl_insert
             [eval_agg_op omega
                (set_empty
                  ((ceq_prod ceq_event_data ceq_enat),
                    (ccompare_prod ccompare_event_data ccompare_enat))
                  (of_phantom
                    (set_impl_proda set_impl_event_data set_impl_enat)))]
             edl_bot
      else (let groups =
              unbox edl_cluster_v (comp (fun a -> Some a) (drop k)) rel in
             edl_image
               (fun g ->
                 (match edl_lookup_table groups g with None -> g
                   | Some ga ->
                     take pos g @
                       eval_agg_op omega (uagg_values f ga) :: drop pos g))
               (unbox edl_keys_table_v groups)));;

let rec dagg_fallback
  args x =
    uagg (dgg_g0 args) (dgg_op args) (dgg_trm args) (dgg_k args) (dgg_p args)
      x;;

let rec dresult_maggauxa
  args xa1 x = match args, xa1, x with args, None, x -> dagg_fallback args x
    | args, Some aux, x -> dresult_maggaux args aux;;

let rec daresult_msaux
  ag sa = (let (s, a) = sa in dresult_maggauxa ag a (gmsaux_in s));;

let rec hsd_result2
  q = (fun () -> (snd (snd (snd (snd (snd (snd (fst q))))))));;

let rec result_d
  args x1 = match args, x1 with args, MSD_imp q -> hsd_result2 q
    | args, MSD_dns s -> (fun () -> (de_gresult_msaux args s))
    | args, MSD_evt a -> (fun () -> (de_gresult_sevt args a))
    | args, MSD_agg (ag, s) -> (fun () -> (daresult_msaux ag s));;

let rec mapping_delete_set_cfi (_A1, _A2)
  = Abs_comp_fun_idem (delete (_A1, _A2));;

let rec mapping_delete_set (_A1, _A2, _A3, _A4)
  m a = (if finite (_A1, _A2, _A3) a
          then set_fold_cfi (_A2, _A3) (mapping_delete_set_cfi (_A3, _A4)) m a
          else failwith "mapping_delete_set: infinite"
                 (fun _ -> mapping_delete_set (_A1, _A2, _A3, _A4) m a));;

let edl_mfilter_table_v :
  ((event_data list -> (event_data list) set -> bool) ->
    ((event_data list), (event_data list) set) mapping ->
      ((event_data list), (event_data list) set) mapping)
    boxed
  = Box (filterc (ccompare_list ccompare_event_data));;

let edl_set_of_idx_v :
  (((event_data list), (event_data list) set) mapping -> (event_data list) set)
    boxed
  = Box (set_of_idx (ccompare_list ccompare_event_data)
          ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data),
            set_impl_list));;

let rec de_dsemi_idx
  msk pos idx x =
    unbox edl_set_of_idx_v
      (unbox edl_mfilter_table_v (fun k _ -> equal_boola (edl_member k x) pos)
        idx);;

let rec de_gjoin_msaux
  args y
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (let pos = args_pos args in
        (if list_all not msk
          then (let take_all = equal_boola (edl_member [] y) pos in
                 (t, (gc, (msk, (data_prev,
                                  (data_in,
                                    ((if take_all then table_in else edl_bot),
                                      ((if take_all then idx_in
 else edl_mempty_table),
((if take_all then tuple_in else edl_mempty_nat),
  ((if take_all then idx_since else edl_mempty_table),
    (if take_all then tuple_since else edl_mempty_nat)))))))))))
          else (if list_all (fun i -> i) msk
                 then (let in_del =
                         (if pos then edl_minus table_in y
                           else edl_inter table_in y)
                         in
                       let tuple_ina =
                         mapping_delete_set
                           (finite_UNIV_list, (ceq_list ceq_event_data),
                             (ccompare_list ccompare_event_data),
                             (equal_list equal_event_data))
                           tuple_in in_del
                         in
                       let tuple_sincea =
                         unbox edl_mfilter_nat_v
                           (fun asa _ -> equal_boola (edl_member asa y) pos)
                           tuple_since
                         in
                        (t, (gc, (msk, (data_prev,
 (data_in,
   (edl_minus table_in in_del,
     (edl_mempty_table, (tuple_ina, (edl_mempty_table, tuple_sincea))))))))))
                 else (let in_del = de_dsemi_idx msk (not pos) idx_in y in
                       let since_del = de_dsemi_idx msk (not pos) idx_since y in
                        (t, (gc, (msk, (data_prev,
 (data_in,
   (edl_minus table_in in_del,
     (unbox edl_mfilter_table_v (fun k _ -> equal_boola (edl_member k y) pos)
        idx_in,
       (mapping_delete_set
          (finite_UNIV_list, (ceq_list ceq_event_data),
            (ccompare_list ccompare_event_data), (equal_list equal_event_data))
          tuple_in in_del,
         (unbox edl_mfilter_table_v
            (fun k _ -> equal_boola (edl_member k y) pos) idx_since,
           mapping_delete_set
             (finite_UNIV_list, (ceq_list ceq_event_data),
               (ccompare_list ccompare_event_data),
               (equal_list equal_event_data))
             tuple_since since_del)))))))))))));;

let rec de_ggc_msaux
  args (nt, (gc, (msk, (data_prev,
                         (data_in,
                           (table_in,
                             (idx_in,
                               (tuple_in, (idx_since, tuple_since)))))))))
    = (let all_tuples =
         sup_setb
           (finite_UNIV_list, cenum_list, (ceq_list ceq_event_data),
             (cproper_interval_list ccompare_event_data), set_impl_list)
           (image
             ((ceq_prod ceq_nat
                (ceq_set
                  (cenum_list, (ceq_list ceq_event_data),
                    (cproper_interval_list
                      ccompare_event_data).ccompare_cproper_interval))),
               (ccompare_prod ccompare_nat
                 (ccompare_set
                   (finite_UNIV_list, (ceq_list ceq_event_data),
                     (cproper_interval_list ccompare_event_data),
                     set_impl_list))))
             ((ceq_set
                (cenum_list, (ceq_list ceq_event_data),
                  (cproper_interval_list
                    ccompare_event_data).ccompare_cproper_interval)),
               (ccompare_set
                 (finite_UNIV_list, (ceq_list ceq_event_data),
                   (cproper_interval_list ccompare_event_data), set_impl_list)),
               set_impl_set)
             snd (set ((ceq_prod ceq_nat
                         (ceq_set
                           (cenum_list, (ceq_list ceq_event_data),
                             (cproper_interval_list
                               ccompare_event_data).ccompare_cproper_interval))),
                        (ccompare_prod ccompare_nat
                          (ccompare_set
                            (finite_UNIV_list, (ceq_list ceq_event_data),
                              (cproper_interval_list ccompare_event_data),
                              set_impl_list))),
                        (set_impl_prod set_impl_nat set_impl_set))
                   (linearize data_prev @ linearize data_in)))
         in
       let tuple_sincea =
         unbox edl_mfilter_nat_v (fun asa _ -> edl_member asa all_tuples)
           tuple_since
         in
        (nt, (nt, (msk, (data_prev,
                          (data_in,
                            (table_in,
                              (idx_in,
                                (tuple_in,
                                  (de_gidx_upd args
                                     (fun _ ->
                                       didx
 (ceq_event_data, ccompare_event_data) msk (unbox edl_keys_nat_v tuple_sincea)),
                                    tuple_sincea))))))))));;

let rec de_ggc_join_msaux
  args y
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (if not (memR (args_ivl args) (minus_nata t gc))
        then de_gjoin_msaux args y
               (de_ggc_msaux args
                 (t, (gc, (msk, (data_prev,
                                  (data_in,
                                    (table_in,
                                      (idx_in,
(tuple_in, (idx_since, tuple_since))))))))))
        else de_gjoin_msaux args y
               (t, (gc, (msk, (data_prev,
                                (data_in,
                                  (table_in,
                                    (idx_in,
                                      (tuple_in,
(idx_since, tuple_since))))))))));;

let rec de_gjoin_sevt
  args x aux =
    (let (t, (_, (_, (_, _)))) = aux in
      (if (if args_pos args then not (unbox edl_is_empty_v x)
            else unbox edl_is_empty_v x)
        then aux
        else (t, (empty_queue, (empty_queue, (edl_mempty_nat, edl_bot))))));;

let rec im_delete _A _B hsh eq q x = im_delete_h _A _B eq q (hsh x) x;;

let rec hsd_del_loop2
  hsh eq p ks h =
    (match ks with [] -> (fun () -> h)
      | k :: r ->
        (if p k then hsd_del_loop2 hsh eq p r h
          else binda (im_delete (heap_list heap_event_data) heap_nat hsh eq h k)
                 (hsd_del_loop2 hsh eq p r)));;

let rec hsd_gjc
  pos x k = (if pos then edl_member k x else not (edl_member k x));;

let rec im_count b = integer_of_nat (size_lista b);;

let rec im_filter_idx _A _B
  p a i n c =
    (if Z.leq n i then (fun () -> c)
      else binda ((fun () -> Array.get a (Z.to_int i)))
             (fun b ->
               (let ba = filtera (fun e -> p (fst (snd e))) b in
                 binda (if Z.equal (im_count ba) (im_count b)
                         then (fun () -> ())
                         else (fun () -> Array.set a (Z.to_int i) ba))
                   (fun _ ->
                     im_filter_idx _A _B p a (Z.add i (Z.of_int 1)) n
                       (Z.sub c (Z.sub (im_count b) (im_count ba)))))));;

let rec im_filter _A _B
  p q = (let (n, (c, a)) = q in
          binda (im_filter_idx _A _B p a Z.zero n c)
            (fun ca -> (fun () -> (n, (ca, a)))));;

let rec hsd_join2
  hsh eq nul args x q =
    (let ((t, (gc, (mL, (mR, (dp, (di, tin)))))), (hin, hsince)) = q in
     let pos = args_pos args in
      (if list_all not mL
        then (if equal_boola pos (edl_member nul x) then (fun () -> q)
               else binda (im_new (heap_list heap_event_data) heap_nat
                            (Z.of_int 16))
                      (fun hina ->
                        binda (im_new (heap_list heap_event_data) heap_nat
                                (Z.of_int 16))
                          (fun hsincea ->
                            (fun () ->
                              ((t, (gc, (mL, (mR, (dp, (di, edl_bot)))))),
                                (hina, hsincea))))))
        else (let in_del = (if pos then edl_minus tin x else edl_inter tin x) in
               binda (hsd_del_loop2 hsh eq (fun k -> not (edl_member k in_del))
                       (unbox edl_csorted_list_of_set_v in_del) hin)
                 (fun hina ->
                   binda (im_filter (heap_list heap_event_data) heap_nat
                           (hsd_gjc pos x) hsince)
                     (fun hsincea ->
                       (fun () ->
                         ((t, (gc, (mL, (mR,
  (dp, (di, edl_minus tin in_del)))))),
                           (hina, hsincea))))))));;

let rec hsd_gc2
  q = (let ((t, (_, (mL, (mR, (dp, (di, tin)))))), (hin, hsince)) = q in
       let all =
         fold (fun p -> edl_union (snd p)) (linearize dp @ linearize di) edl_bot
         in
        binda (im_filter (heap_list heap_event_data) heap_nat
                (fun k -> edl_member k all) hsince)
          (fun hsincea ->
            (fun () ->
              ((t, (t, (mL, (mR, (dp, (di, tin)))))), (hin, hsincea)))));;

let rec hsd_gc_join2
  hsh eq nul args x q =
    (let ((t, (gc, (_, (_, (_, (_, _)))))), (_, _)) = q in
      (if not (memR (args_ivl args) (minus_nata t gc))
        then binda (hsd_gc2 q) (hsd_join2 hsh eq nul args x)
        else hsd_join2 hsh eq nul args x q));;

let rec gjoin_msaux_del (_A1, _A2, _A3)
  args y
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (let pos = args_pos args in
        (if list_all not msk
          then (let take_all =
                  equal_boola
                    (member ((ceq_list _A1), (ccompare_list _A2)) [] y) pos
                  in
                 ((t, (gc, (msk, (data_prev,
                                   (data_in,
                                     ((if take_all then table_in
else set_empty ((ceq_list _A1), (ccompare_list _A2))
       (of_phantom set_impl_lista)),
                                       ((if take_all then idx_in
  else mapping_empty (ccompare_list _A2) (of_phantom mapping_impl_lista)),
 ((if take_all then tuple_in
    else mapping_empty (ccompare_list _A2) (of_phantom mapping_impl_lista)),
   ((if take_all then idx_since
      else mapping_empty (ccompare_list _A2) (of_phantom mapping_impl_lista)),
     (if take_all then tuple_since
       else mapping_empty (ccompare_list _A2)
              (of_phantom mapping_impl_lista))))))))))),
                   (if take_all
                     then Some (set_empty ((ceq_list _A1), (ccompare_list _A2))
                                 (of_phantom set_impl_lista))
                     else None)))
          else (if list_all (fun i -> i) msk
                 then (let in_del =
                         (if pos
                           then minus_set ((ceq_list _A1), (ccompare_list _A2))
                                  table_in y
                           else inf_seta ((ceq_list _A1), (ccompare_list _A2))
                                  table_in y)
                         in
                       let tuple_ina =
                         mapping_delete_set
                           (finite_UNIV_list, (ceq_list _A1),
                             (ccompare_list _A2), (equal_list _A3))
                           tuple_in in_del
                         in
                       let tuple_sincea =
                         filterc (ccompare_list _A2)
                           (fun asa _ ->
                             equal_boola
                               (member ((ceq_list _A1), (ccompare_list _A2)) asa
                                 y)
                               pos)
                           tuple_since
                         in
                        ((t, (gc, (msk, (data_prev,
  (data_in,
    (minus_set ((ceq_list _A1), (ccompare_list _A2)) table_in in_del,
      (mapping_empty (ccompare_list _A2) (of_phantom mapping_impl_lista),
        (tuple_ina,
          (mapping_empty (ccompare_list _A2) (of_phantom mapping_impl_lista),
            tuple_sincea))))))))),
                          Some in_del))
                 else (let in_del = dsemi_idx (_A1, _A2) msk (not pos) idx_in y
                         in
                       let since_del =
                         dsemi_idx (_A1, _A2) msk (not pos) idx_since y in
                        ((t, (gc, (msk, (data_prev,
  (data_in,
    (minus_set ((ceq_list _A1), (ccompare_list _A2)) table_in in_del,
      (filterc (ccompare_list _A2)
         (fun k _ ->
           equal_boola (member ((ceq_list _A1), (ccompare_list _A2)) k y) pos)
         idx_in,
        (mapping_delete_set
           (finite_UNIV_list, (ceq_list _A1), (ccompare_list _A2),
             (equal_list _A3))
           tuple_in in_del,
          (filterc (ccompare_list _A2)
             (fun k _ ->
               equal_boola (member ((ceq_list _A1), (ccompare_list _A2)) k y)
                 pos)
             idx_since,
            mapping_delete_set
              (finite_UNIV_list, (ceq_list _A1), (ccompare_list _A2),
                (equal_list _A3))
              tuple_since since_del))))))))),
                          Some in_del)))));;

let rec ggc_msaux (_A1, _A2)
  args (nt, (gc, (msk, (data_prev,
                         (data_in,
                           (table_in,
                             (idx_in,
                               (tuple_in, (idx_since, tuple_since)))))))))
    = (let all_tuples =
         sup_setb
           (finite_UNIV_list, cenum_list, (ceq_list _A1),
             (cproper_interval_list _A2), set_impl_list)
           (image
             ((ceq_prod ceq_nat
                (ceq_set
                  (cenum_list, (ceq_list _A1),
                    (cproper_interval_list _A2).ccompare_cproper_interval))),
               (ccompare_prod ccompare_nat
                 (ccompare_set
                   (finite_UNIV_list, (ceq_list _A1),
                     (cproper_interval_list _A2), set_impl_list))))
             ((ceq_set
                (cenum_list, (ceq_list _A1),
                  (cproper_interval_list _A2).ccompare_cproper_interval)),
               (ccompare_set
                 (finite_UNIV_list, (ceq_list _A1), (cproper_interval_list _A2),
                   set_impl_list)),
               set_impl_set)
             snd (set ((ceq_prod ceq_nat
                         (ceq_set
                           (cenum_list, (ceq_list _A1),
                             (cproper_interval_list
                               _A2).ccompare_cproper_interval))),
                        (ccompare_prod ccompare_nat
                          (ccompare_set
                            (finite_UNIV_list, (ceq_list _A1),
                              (cproper_interval_list _A2), set_impl_list))),
                        (set_impl_prod set_impl_nat set_impl_set))
                   (linearize data_prev @ linearize data_in)))
         in
       let tuple_sincea =
         filterc (ccompare_list _A2)
           (fun asa _ ->
             member ((ceq_list _A1), (ccompare_list _A2)) asa all_tuples)
           tuple_since
         in
        (nt, (nt, (msk, (data_prev,
                          (data_in,
                            (table_in,
                              (idx_in,
                                (tuple_in,
                                  (gidx_upd _A2 args
                                     (fun _ ->
                                       didx (_A1, _A2) msk
 (keys (cenum_list, (ceq_list _A1), (ccompare_list _A2), set_impl_list)
   tuple_sincea)),
                                    tuple_sincea))))))))));;

let rec ggc_join_msaux_del (_A1, _A2, _A3)
  args y
    (t, (gc, (msk, (data_prev,
                     (data_in,
                       (table_in,
                         (idx_in, (tuple_in, (idx_since, tuple_since)))))))))
    = (if not (memR (args_ivl args) (minus_nata t gc))
        then gjoin_msaux_del (_A1, _A2, _A3) args y
               (ggc_msaux (_A1, _A2) args
                 (t, (gc, (msk, (data_prev,
                                  (data_in,
                                    (table_in,
                                      (idx_in,
(tuple_in, (idx_since, tuple_since))))))))))
        else gjoin_msaux_del (_A1, _A2, _A3) args y
               (t, (gc, (msk, (data_prev,
                                (data_in,
                                  (table_in,
                                    (idx_in,
                                      (tuple_in,
(idx_since, tuple_since))))))))));;

let rec dinit_maggaux
  args =
    (match (fst (dgg_op args), snd (dgg_op args))
      with (Agg_Cnt, _) -> (true, DCntAux edl_mempty_nat)
      | (Agg_Min, TInt) ->
        (true,
          DRankAux
            (mapping_empty (ccompare_list ccompare_event_data)
               (of_phantom mapping_impl_lista),
              IntT))
      | (Agg_Min, TFloat) -> (false, DCntAux edl_mempty_nat)
      | (Agg_Min, TString) ->
        (true,
          DRankAux
            (mapping_empty (ccompare_list ccompare_event_data)
               (of_phantom mapping_impl_lista),
              StringT))
      | (Agg_Max, TInt) ->
        (true,
          DRankAux
            (mapping_empty (ccompare_list ccompare_event_data)
               (of_phantom mapping_impl_lista),
              IntT))
      | (Agg_Max, TFloat) -> (false, DCntAux edl_mempty_nat)
      | (Agg_Max, TString) ->
        (true,
          DRankAux
            (mapping_empty (ccompare_list ccompare_event_data)
               (of_phantom mapping_impl_lista),
              StringT))
      | (Agg_Sum, TInt) ->
        (true,
          DSumAux
            (mapping_empty (ccompare_list ccompare_event_data)
              (of_phantom mapping_impl_lista)))
      | (Agg_Sum, TFloat) -> (false, DCntAux edl_mempty_nat)
      | (Agg_Sum, TString) -> (false, DCntAux edl_mempty_nat)
      | (Agg_Avg, TInt) ->
        (true,
          DSumAux
            (mapping_empty (ccompare_list ccompare_event_data)
              (of_phantom mapping_impl_lista)))
      | (Agg_Avg, TFloat) -> (false, DCntAux edl_mempty_nat)
      | (Agg_Avg, TString) -> (false, DCntAux edl_mempty_nat)
      | (Agg_Med, TInt) -> (false, DCntAux edl_mempty_nat)
      | (Agg_Med, TFloat) ->
        (true,
          DRankAux
            (mapping_empty (ccompare_list ccompare_event_data)
               (of_phantom mapping_impl_lista),
              IntT))
      | (Agg_Med, TString) -> (false, DCntAux edl_mempty_nat));;

let rec dinit_maggauxa
  args =
    (match dinit_maggaux args with (true, aux) -> Some aux
      | (false, _) -> None);;

let rec dajoin_msaux
  args ag y sa =
    (let (s, a) = sa in
     let (s1, d) =
       ggc_join_msaux_del
         (ceq_event_data, ccompare_event_data, equal_event_data) args y s
       in
      (s1, (match d with None -> dinit_maggauxa ag
             | Some da -> ddelete_maggauxa ag da a)));;

let rec join_d
  args x xa2 = match args, x, xa2 with
    args, x, MSD_imp q ->
      binda (hsd_gc_join2
              (fun t -> let rec go h l = (match l with [] -> h | EInt z :: r -> go (h * 31 + Z.hash z) r | EFloat f :: r -> go (h * 31 + Hashtbl.hash f) r | EString s :: r -> go (h * 31 + Hashtbl.hash s) r) in Z.of_int ((go 17 t) land 1073741823))
              ueq [] args x q)
        (fun qa -> (fun () -> (MSD_imp qa)))
    | args, x, MSD_dns s -> (fun () -> (MSD_dns (de_ggc_join_msaux args x s)))
    | args, x, MSD_evt a -> (fun () -> (MSD_evt (de_gjoin_sevt args x a)))
    | args, x, MSD_agg (ag, s) ->
        (fun () -> (MSD_agg (ag, dajoin_msaux args ag x s)));;

let rec eval_since_d
  args rs buf aux =
    (let (xs, (ys, (ts, skew))) = buf in
      (match mbuf_t_cases ys
        with (None, _) ->
          (match mbuf_t_cases xs
            with (None, _) ->
              (fun () ->
                (rev rs, ((mbuf_t_empty, (mbuf_t_empty, (ts, skew))), aux)))
            | (Some x, xsa) ->
              (match mbuf_t_cases ts
                with (None, _) ->
                  (fun () ->
                    (rev rs,
                      ((mbuf_t_Cons x xsa,
                         (mbuf_t_empty, (mbuf_t_empty, skew))),
                        aux)))
                | (Some t, tsa) ->
                  (if skew || memL (args_ivl args) zero_nata
                    then (fun () ->
                           (rev rs,
                             ((mbuf_t_Cons x xsa,
                                (mbuf_t_empty, (mbuf_t_Cons t tsa, skew))),
                               aux)))
                    else binda (add_new_ts_d args t aux)
                           (fun auxa ->
                             binda (join_d args x auxa)
                               (fun auxb ->
                                 binda (result_d args auxb)
                                   (fun r ->
                                     (fun () ->
                                       (rev (r :: rs),
 ((xsa, (mbuf_t_empty, (tsa, true))), auxb)))))))))
        | (Some y, ysa) ->
          (if skew
            then binda (add_new_table_d args y aux)
                   (eval_since_d args rs (xs, (ysa, (ts, false))))
            else (match mbuf_t_cases xs
                   with (None, _) ->
                     (fun () ->
                       (rev rs,
                         ((mbuf_t_empty, (mbuf_t_Cons y ysa, (ts, skew))),
                           aux)))
                   | (Some x, xsa) ->
                     (match mbuf_t_cases ts
                       with (None, tsa) ->
                         (fun () ->
                           (rev rs,
                             ((mbuf_t_Cons x xsa,
                                (mbuf_t_Cons y ysa, (tsa, skew))),
                               aux)))
                       | (Some t, tsa) ->
                         binda (add_new_ts_d args t aux)
                           (fun auxa ->
                             binda (join_d args x auxa)
                               (fun auxb ->
                                 binda (add_new_table_d args y auxb)
                                   (fun auxc ->
                                     binda (result_d args auxc)
                                       (fun r ->
 eval_since_d args (r :: rs) (xsa, (ysa, (tsa, false))) auxc)))))))));;

let rec umebufn_add
  xsa xs = mapa (fun (a, b) -> mbuf_t_append a b) (zip xs xsa);;

let edl_impl_of_tuples_v :
  (((event_data list), ((event_data list) list)) mapping_rbt ->
    ((event_data list), ((event_data list) list)) rbt)
    boxed
  = Box (impl_ofa (ccompare_list ccompare_event_data));;

let rec edl_rbt_lookup_tuples
  t k = edl_rbtc_lookup (unbox edl_impl_of_tuples_v t) k;;

let rec edl_lookup_tuples
  = function RBT_Mapping t -> edl_rbt_lookup_tuples t
    | Assoc_List_Mapping al -> lookup (equal_list equal_event_data) al;;

let rec de_gprobe_step_l
  p rk m y acc =
    (match edl_lookup_tuples m (dproj rk y) with None -> acc
      | Some l -> fold (fun x -> edl_insert (dmerge p x y)) l acc);;

let rec de_gprobe_step
  p msk m a acc =
    (match edl_lookup_tuples m (dproj msk a) with None -> acc
      | Some l -> fold (fun b -> edl_insert (dmerge p a b)) l acc);;

let edl_card_v : ((event_data list) set -> nat) boxed
  = Box (card (card_UNIV_list, (ceq_list ceq_event_data),
                (ccompare_list ccompare_event_data)));;

let edl_mempty_tuples : ((event_data list), ((event_data list) list)) mapping
  = RBT_Mapping (emptyc (ccompare_list ccompare_event_data));;

let rec edl_rbt_insert_tuples
  xc xd xe =
    Mapping_RBTa (edl_rbtc_insert xc xd (unbox edl_impl_of_tuples_v xe));;

let rec edl_update_tuples
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t -> RBT_Mapping (edl_rbt_insert_tuples k v t)
    | k, v, Assoc_List_Mapping al ->
        Assoc_List_Mapping (updatea (equal_list equal_event_data) k v al)
    | k, v, Mapping m ->
        Mapping (fun_upd (equal_list equal_event_data) m k (Some v));;

let rec de_gindex_step
  msk b m =
    (let k = dproj msk b in
      (match edl_lookup_tuples m k with None -> edl_update_tuples k [b] m
        | Some l -> edl_update_tuples k (b :: l) m));;

let rec csl (_A1, _A2, _A3)
  x = (if finite (_A1, _A2, _A3) x then csorted_list_of_set (_A2, _A3) x
        else []);;

let rec de_gindex
  msk b =
    fold (de_gindex_step msk)
      (csl (finite_UNIV_list, (ceq_list ceq_event_data),
             (ccompare_list ccompare_event_data))
        b)
      edl_mempty_tuples;;

let rec de_ggen_join
  p lk rk a b =
    (if less_eq_nat (unbox edl_card_v a) (unbox edl_card_v b)
      then (let m = de_gindex lk a in
             fold (de_gprobe_step_l p rk m)
               (csl (finite_UNIV_list, (ceq_list ceq_event_data),
                      (ccompare_list ccompare_event_data))
                 b)
               edl_bot)
      else (let m = de_gindex rk b in
             fold (de_gprobe_step p lk m)
               (csl (finite_UNIV_list, (ceq_list ceq_event_data),
                      (ccompare_list ccompare_event_data))
                 a)
               edl_bot));;

let rec de_gbin_join0
  x0 a pos b = match x0, a, pos, b with
    DJEq, a, pos, b -> (if pos then edl_inter a b else edl_minus a b)
    | DJEmp, a, pos, b ->
        (if equal_boola pos (edl_member [] b) then a else edl_bot)
    | DJSub msk, a, pos, b -> de_dsemi msk pos a b
    | DJSup msk, a, pos, b ->
        (if pos then edl_filter (fun ba -> edl_member (dproj msk ba) a) b
          else a)
    | DJGen (p, lk, rk), a, pos, b ->
        (if pos then de_ggen_join p lk rk a b else a);;

let rec de_gbin_join
  pl a pos b =
    (if unbox edl_is_empty_v a then edl_bot
      else (if unbox edl_is_empty_v b then (if pos then edl_bot else a)
             else de_gbin_join0 pl a pos b));;

let djidx_new_v :
  (Z.t ->
    (unit ->
      (Z.t *
        (Z.t *
          ((Z.t * (event_data list * (event_data list) list)) list) array))))
    boxed
  = Box (im_new (heap_list heap_event_data)
          (heap_list (heap_list heap_event_data)));;

let rec heap_join_ok
  idx = Z.leq (Z.of_int !ConfigImp.heap_join_min)
          (integer_of_nat (size_lista idx));;

let djidx_lookup_h_v :
  ((event_data list -> event_data list -> bool) ->
    Z.t * (Z.t *
            ((Z.t * (event_data list * (event_data list) list)) list) array) ->
      Z.t -> event_data list -> (unit -> (((event_data list) list) option)))
    boxed
  = Box (im_lookup_h (heap_list heap_event_data)
          (heap_list (heap_list heap_event_data)));;

let rec dprobe_r
  p lk q xs acc =
    (match xs with [] -> (fun () -> acc)
      | x :: r ->
        (let k = dproj lk x in
          binda (unbox djidx_lookup_h_v ueq q
                  ((fun t -> let rec go h l = (match l with [] -> h | EInt z :: r -> go (h * 31 + Z.hash z) r | EFloat f :: r -> go (h * 31 + Hashtbl.hash f) r | EString s :: r -> go (h * 31 + Hashtbl.hash s) r) in Z.of_int ((go 17 t) land 1073741823))
                    k)
                  k)
            (fun v ->
              dprobe_r p lk q r
                (match v with None -> acc
                  | Some l ->
                    fold (fun y -> edl_insert (dmerge p x y)) l acc))));;

let rec dprobe_l
  p rk q ys acc =
    (match ys with [] -> (fun () -> acc)
      | y :: r ->
        (let k = dproj rk y in
          binda (unbox djidx_lookup_h_v ueq q
                  ((fun t -> let rec go h l = (match l with [] -> h | EInt z :: r -> go (h * 31 + Z.hash z) r | EFloat f :: r -> go (h * 31 + Hashtbl.hash f) r | EString s :: r -> go (h * 31 + Hashtbl.hash s) r) in Z.of_int ((go 17 t) land 1073741823))
                    k)
                  k)
            (fun v ->
              dprobe_l p rk q r
                (match v with None -> acc
                  | Some l ->
                    fold (fun x -> edl_insert (dmerge p x y)) l acc))));;

let djidx_update_h_v :
  ((event_data list -> event_data list -> bool) ->
    Z.t * (Z.t *
            ((Z.t * (event_data list * (event_data list) list)) list) array) ->
      Z.t ->
        event_data list ->
          (event_data list) list ->
            (unit ->
              (Z.t *
                (Z.t *
                  ((Z.t * (event_data list * (event_data list) list)) list)
                    array))))
    boxed
  = Box (im_update_h (heap_list heap_event_data)
          (heap_list (heap_list heap_event_data)));;

let rec didx_ins
  msk xs q =
    (match xs with [] -> (fun () -> q)
      | x :: r ->
        (let k = dproj msk x in
         let h =
           (fun t -> let rec go h l = (match l with [] -> h | EInt z :: r -> go (h * 31 + Z.hash z) r | EFloat f :: r -> go (h * 31 + Hashtbl.hash f) r | EString s :: r -> go (h * 31 + Hashtbl.hash s) r) in Z.of_int ((go 17 t) land 1073741823))
             k
           in
          binda (unbox djidx_lookup_h_v ueq q h k)
            (fun v ->
              binda (unbox djidx_update_h_v ueq q h k
                      (match v with None -> [x] | Some a -> x :: a))
                (didx_ins msk r))));;

let rec dbin_join_h
  x0 a pos b = match x0, a, pos, b with
    DJGen (p, lk, rk), a, pos, b ->
      (if not !ConfigImp.dense_heap_join ||
            (not pos || (unbox edl_is_empty_v a || unbox edl_is_empty_v b))
        then (fun () -> (de_gbin_join (DJGen (p, lk, rk)) a pos b))
        else (let xs =
                csl (finite_UNIV_list, (ceq_list ceq_event_data),
                      (ccompare_list ccompare_event_data))
                  a
                in
              let ys =
                csl (finite_UNIV_list, (ceq_list ceq_event_data),
                      (ccompare_list ccompare_event_data))
                  b
                in
               (if less_eq_nat (size_lista ys) (size_lista xs)
                 then (if not (heap_join_ok ys)
                        then (fun () ->
                               (de_gbin_join (DJGen (p, lk, rk)) a pos b))
                        else binda (unbox djidx_new_v
                                     (Z.mul (Z.of_int 2)
                                       (integer_of_nat (size_lista ys))))
                               (fun q ->
                                 binda (didx_ins rk ys q)
                                   (fun qa -> dprobe_r p lk qa xs edl_bot)))
                 else (if not (heap_join_ok xs)
                        then (fun () ->
                               (de_gbin_join (DJGen (p, lk, rk)) a pos b))
                        else binda (unbox djidx_new_v
                                     (Z.mul (Z.of_int 2)
                                       (integer_of_nat (size_lista xs))))
                               (fun q ->
                                 binda (didx_ins lk xs q)
                                   (fun qa -> dprobe_l p rk qa ys edl_bot))))))
    | DJEq, a, pos, b -> (fun () -> (de_gbin_join DJEq a pos b))
    | DJEmp, a, pos, b -> (fun () -> (de_gbin_join DJEmp a pos b))
    | DJSub v, a, pos, b -> (fun () -> (de_gbin_join (DJSub v) a pos b))
    | DJSup v, a, pos, b -> (fun () -> (de_gbin_join (DJSup v) a pos b));;

let rec dands_pos_h
  x0 t us = match x0, t, us with [], t, us -> (fun () -> t)
    | p :: ps, t, [] -> (fun () -> t)
    | p :: ps, t, u :: us ->
        binda (dbin_join_h p t true u) (fun ta -> dands_pos_h ps ta us);;

let rec dands_neg_h
  x0 t us = match x0, t, us with [], t, us -> (fun () -> t)
    | p :: ps, t, [] -> (fun () -> t)
    | p :: ps, t, u :: us ->
        binda (dbin_join_h p t false u) (fun ta -> dands_neg_h ps ta us);;

let rec dmulti_join
  ps ns us =
    (match us with [] -> (fun () -> edl_bot)
      | t :: r ->
        binda (dands_pos_h ps t (take (size_lista ps) r))
          (fun ta -> dands_neg_h ns ta (drop (size_lista ps) r)));;

let rec de_gevt_extend
  args ts0 win rest bend cnt cur =
    (if not bend then (win, (rest, (bend, (cnt, cur))))
      else (match safe_hd rest
             with (None, resta) -> (win, (resta, (bend, (cnt, cur))))
             | (Some e, resta) ->
               (if memR (args_ivl args) (minus_nata (fst e) ts0)
                 then (let (a, b) = de_gevt_add (fst (snd e)) (cnt, cur) in
                        de_gevt_extend args ts0 (append_queue e win)
                          (tl_queue resta) (snd (snd e)) a b)
                 else (win, (resta, (bend, (cnt, cur)))))));;

let rec de_gevt_step
  args ts0 aux =
    (let (nts, (win, (rest, (len, (bend, (cnt, (cur, dn))))))) = aux in
     let (wina, (resta, (benda, (cnta, cura)))) =
       de_gevt_extend args ts0 win rest bend cnt cur in
      (match safe_hd wina
        with (None, winb) ->
          (match safe_hd resta
            with (None, restb) ->
              (tl_queue nts,
                (winb,
                  (restb,
                    (minus_nata len one_nata,
                      (benda, (cnta, (cura, edl_bot :: dn)))))))
            | (Some _, restb) ->
              (tl_queue nts,
                (winb,
                  (tl_queue restb,
                    (minus_nata len one_nata,
                      (benda, (cnta, (cura, edl_bot :: dn))))))))
        | (Some e, winb) ->
          (let winc = tl_queue winb in
           let (cntb, curaa) = de_gevt_del (fst (snd e)) (cnta, cura) in
           let bendb = (if is_emptya winc then true else benda) in
            (tl_queue nts,
              (winc,
                (resta,
                  (minus_nata len one_nata,
                    (bendb, (cntb, (curaa, cura :: dn))))))))));;

let rec de_gevt_shift
  args nt aux =
    (let (nts, (win, (rest, (len, (bend, (cnt, (cur, dn))))))) = aux in
      (match safe_hd nts
        with (None, ntsa) ->
          (ntsa, (win, (rest, (len, (bend, (cnt, (cur, dn)))))))
        | (Some ts0, ntsa) ->
          (if memR (args_ivl args) (minus_nata nt ts0) ||
                equal_nata len zero_nata
            then (ntsa, (win, (rest, (len, (bend, (cnt, (cur, dn)))))))
            else de_gevt_shift args nt
                   (de_gevt_step args ts0
                     (ntsa,
                       (win, (rest, (len, (bend, (cnt, (cur, dn)))))))))));;

let rec de_gadd_new_evt
  args rel1 rel2 nt aux =
    (let (nts, (win, (rest, (len, (bend, (cnt, (cur, dn))))))) =
       de_gevt_shift args nt aux in
     let b =
       (if args_pos args then not (unbox edl_is_empty_v rel1)
         else unbox edl_is_empty_v rel1)
       in
      (append_queue nt nts,
        (win, (append_queue (nt, (rel2, b)) rest,
                (plus_nata len one_nata, (bend, (cnt, (cur, dn))))))));;

let rec dq_nf (Dq (x1, x2, x3, x4)) = x3;;

let rec dq_nb (Dq (x1, x2, x3, x4)) = x4;;

let rec dq_f (Dq (x1, x2, x3, x4)) = x1;;

let rec dq_b (Dq (x1, x2, x3, x4)) = x2;;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if equal_nata i zero_nata then y :: xs
          else x :: list_update xs (minus_nata i one_nata) y);;

let rec dq_upd
  d k x =
    (if less_nat k (dq_nf d)
      then Dq (list_update (dq_f d) k x, dq_b d, dq_nf d, dq_nb d)
      else Dq (dq_f d,
                list_update (dq_b d)
                  (minus_nata (minus_nata (dq_nb d) one_nata)
                    (minus_nata k (dq_nf d)))
                  x,
                dq_nf d, dq_nb d));;

let rec dq_len d = plus_nata (dq_nf d) (dq_nb d);;

let rec dq_nth_l
  d k z =
    (if less_nat k (dq_nf d)
      then (if less_nat k (size_lista (dq_f d)) then nth (dq_f d) k else z)
      else (let j =
              minus_nata (minus_nata (dq_nb d) one_nata)
                (minus_nata k (dq_nf d))
              in
             (if less_nat j (size_lista (dq_b d)) then nth (dq_b d) j
               else z)));;

let rec gupd_nested_step_dq (_B1, _B2, _B3)
  base d f x dq =
    (let (k, ka) = x in
      (if less_eq_nat base k && less_nat (minus_nata k base) (dq_len dq)
        then (let i = minus_nata k base in
              let m = dq_nth_l dq i (emptya (_B1, _B3)) in
               dq_upd dq i
                 (match lookupa (_B1, _B2) m ka
                   with None -> updateb (_B1, _B2) ka d m
                   | Some v -> updateb (_B1, _B2) ka (f v) m))
        else dq));;

let rec ed_max_nat a b = (if less_eq_nat a b then b else a);;

let rec max_tstp
  x0 x1 = match x0, x1 with Inl tsa, Inl ts -> Inl (ed_max_nat tsa ts)
    | Inr tpa, Inr tp -> Inr (ed_max_nat tpa tp)
    | Inl ts, Inr v -> Inl ts
    | Inr v, Inl ts -> Inl ts;;

let rec de_guntil_step_dq
  pa d t0 p acc =
    (let (tbl, (a2, res)) = acc in
      (if pa (fst p)
        then (edl_insert (snd p) tbl,
               (gupd_nested_step_dq
                  ((ccompare_list ccompare_event_data),
                    (equal_list equal_event_data), mapping_impl_list)
                  t0 d (max_tstp d) p a2,
                 (if equal_nata (fst p) t0 then edl_insert (snd p) res
                   else res)))
        else acc));;

let rec de_guntil_elem_step_dq
  a1_map msk pos tp len inz p d asa acc =
    (let acca =
       (if inz then de_guntil_step_dq p d (minus_nata tp len) (tp, asa) acc
         else acc)
       in
      (match edl_lookup_nat a1_map (dproj msk asa)
        with None ->
          (if not pos
            then de_guntil_step_dq p d (minus_nata tp len)
                   (minus_nata tp len, asa) acca
            else acca)
        | Some tpa ->
          de_guntil_step_dq p d (minus_nata tp len)
            (if pos then (ed_max_nat (minus_nata tp len) tpa, asa)
              else (ed_max_nat (minus_nata tp len) (plus_nata tpa one_nata),
                     asa))
            acca));;

let edl_mempty_tstp : ((event_data list), (nat, nat) sum) mapping
  = RBT_Mapping (emptyc (ccompare_list ccompare_event_data));;

let rec dq_push
  x d = (if null (dq_f d)
          then Dq (rev (x :: dq_b d), [], plus_nata (dq_nb d) one_nata,
                    zero_nata)
          else Dq (dq_f d, x :: dq_b d, dq_nf d,
                    plus_nata (dq_nb d) one_nata));;

let edl_impl_of_tstp_v :
  (((event_data list), (nat, nat) sum) mapping_rbt ->
    ((event_data list), (nat, nat) sum) rbt)
    boxed
  = Box (impl_ofa (ccompare_list ccompare_event_data));;

let rec edl_rbt_lookup_tstp
  t k = edl_rbtc_lookup (unbox edl_impl_of_tstp_v t) k;;

let rec edl_lookup_tstp
  = function RBT_Mapping t -> edl_rbt_lookup_tstp t
    | Assoc_List_Mapping al -> lookup (equal_list equal_event_data) al;;

let edl_keys_tstp_v :
  (((event_data list), (nat, nat) sum) mapping -> (event_data list) set) boxed
  = Box (keys (cenum_list, (ceq_list ceq_event_data),
                (ccompare_list ccompare_event_data), set_impl_list));;

let rec dq_norm
  d = (if null (dq_f d)
        then (let h = divide_nata (dq_nb d) (nat_of_integer (Z.of_int 2)) in
               Dq (rev (drop h (dq_b d)), take h (dq_b d),
                    minus_nata (dq_nb d) h, h))
        else d);;

let rec dq_tl
  d = (let da = dq_norm d in
        dq_norm
          (Dq (tla (dq_f da), dq_b da, minus_nata (dq_nf da) one_nata,
                dq_nb da)));;

let rec ts_tp_lt
  i ts tp tstp =
    (match tstp with Inl tsa -> memL i (minus_nata tsa ts)
      | Inr a -> less_eq_nat tp a);;

let rec dq_hd_s
  d z = (match dq_f d
          with [] -> (match dq_b d with [] -> z | _ :: _ -> last (dq_b d))
          | x :: _ -> x);;

let rec de_geval_step_dq
  args (tp, (tss, (tables,
                    (len, (maskL,
                            (maskR,
                              (result, (a1_map, (a2_dq, (tstp_dq, dn))))))))))
    = (let (Some _, tssa) = safe_hd tss in
       let m = dq_hd_s a2_dq edl_mempty_tstp in
       let i = args_ivl args in
       let t = result in
       let tssb = tl_queue tssa in
       let (ts, tssc) =
         (match safe_hd tssb with (None, tssc) -> (zero_nata, tssc)
           | (Some ts, tssc) -> (ts, tssc))
         in
       let (tablesa, taken) =
         takedropWhile_queue
           (fun (_, tstp) ->
             not (ts_tp_lt i ts (plus_nata (minus_nata tp len) one_nata) tstp))
           tables
         in
       let to_del_approx =
         sup_setb
           (finite_UNIV_list, cenum_list, (ceq_list ceq_event_data),
             (cproper_interval_list ccompare_event_data), set_impl_list)
           (set ((ceq_set
                   (cenum_list, (ceq_list ceq_event_data),
                     (cproper_interval_list
                       ccompare_event_data).ccompare_cproper_interval)),
                  (ccompare_set
                    (finite_UNIV_list, (ceq_list ceq_event_data),
                      (cproper_interval_list ccompare_event_data),
                      set_impl_list)),
                  set_impl_set)
             (mapa fst taken))
         in
       let to_del =
         edl_filter
           (fun x ->
             (match edl_lookup_tstp m x with None -> false
               | Some tstp ->
                 not (ts_tp_lt i ts (plus_nata (minus_nata tp len) one_nata)
                       tstp)))
           to_del_approx
         in
       let ma =
         mapping_delete_set
           (finite_UNIV_list, (ceq_list ceq_event_data),
             (ccompare_list ccompare_event_data), (equal_list equal_event_data))
           m to_del
         in
       let a2_dqa = dq_tl a2_dq in
       let maa = dq_hd_s a2_dqa edl_mempty_tstp in
       let resulta =
         (if equal_nata len one_nata then edl_bot
           else edl_union (edl_minus result to_del) (unbox edl_keys_tstp_v maa))
         in
       let a2_dqb =
         dq_upd a2_dqa zero_nata
           (if equal_nata len one_nata then edl_mempty_tstp
             else combine (ccompare_list ccompare_event_data) max_tstp ma maa)
         in
       let tstp_dqa = dq_tl tstp_dq in
        (tp, (tssc,
               (tablesa,
                 (minus_nata len one_nata,
                   (maskL,
                     (maskR,
                       (resulta,
                         (a1_map, (a2_dqb, (tstp_dqa, t :: dn)))))))))));;

let rec takeWhile_queue
  f q = (match safe_hd q with (None, qa) -> (qa, qa)
          | (Some a, qa) ->
            (if f a
              then (let (qaa, _) = takeWhile_queue f (tl_queue qa) in
                     (prepend_queue a qaa, qa))
              else (empty_queue, qa)));;

let rec de_gshift_dq
  args nt
    (tp, (tss, (tables,
                 (len, (maskL,
                         (maskR,
                           (result, (a1_map, (a2_dq, (tstp_dq, dn))))))))))
    = (let (tss_queue, tssa) =
         takeWhile_queue (fun t -> not (memR (args_ivl args) (minus_nata nt t)))
           tss
         in
        foldl (fun aux _ -> de_geval_step_dq args aux)
          (tp, (tssa,
                 (tables,
                   (len, (maskL,
                           (maskR,
                             (result, (a1_map, (a2_dq, (tstp_dq, dn))))))))))
          (linearize tss_queue));;

let rec dq_nth
  d k = (if less_nat k (dq_nf d) then nth (dq_f d) k
          else nth (dq_b d)
                 (minus_nata (minus_nata (dq_nb d) one_nata)
                   (minus_nata k (dq_nf d))));;

let rec dq_nth_s d k z = (if less_nat k (dq_len d) then dq_nth d k else z);;

let rec de_gadd_new_dq
  args msk rel1 rel2 nt aux =
    (let (tp, (tss, (tables,
                      (len, (maskL,
                              (maskR,
                                (result, (a1_map, (a2_dq, (tstp_dq, dn))))))))))
       = de_gshift_dq args nt aux in
     let i = args_ivl args in
     let pos = args_pos args in
     let inz = memL i zero_nata in
     let new_tstp = (if inz then Inr tp else Inl nt) in
     let tstp_dqa = dq_push nt tstp_dq in
     let p =
       (fun t ->
         memL i
           (minus_nata nt
             (dq_nth_s tstp_dqa (minus_nata t (minus_nata tp len)) zero_nata)))
       in
     let (tbl, (a2_dqa, resulta)) =
       fold (de_guntil_elem_step_dq a1_map msk pos tp len inz p new_tstp)
         (csl (finite_UNIV_list, (ceq_list ceq_event_data),
                (ccompare_list ccompare_event_data))
           rel2)
         (edl_bot, (a2_dq, result))
       in
     let tablesa = append_queue (tbl, new_tstp) tables in
     let a2_dqb = dq_push edl_mempty_tstp a2_dqa in
     let a1_mapa =
       (if pos
         then unbox edl_mfilter_nat_v (fun asa _ -> edl_member asa rel1)
                (unbox edl_upd_set_nat_v a1_map (fun _ -> tp)
                  (edl_filter (fun k -> is_none (edl_lookup_nat a1_map k))
                    rel1))
         else unbox edl_upd_set_nat_v a1_map (fun _ -> tp) rel1)
       in
     let tssa = append_queue nt tss in
      (plus_nata tp one_nata,
        (tssa,
          (tablesa,
            (plus_nata len one_nata,
              (maskL,
                (maskR, (resulta, (a1_mapa, (a2_dqb, (tstp_dqa, dn)))))))))));;

let edl_mfilter_tstp_v :
  ((event_data list -> (nat, nat) sum -> bool) ->
    ((event_data list), (nat, nat) sum) mapping ->
      ((event_data list), (nat, nat) sum) mapping)
    boxed
  = Box (filterc (ccompare_list ccompare_event_data));;

let rec gaeval_step_dq
  args ag
    ((tp, (tss, (tables,
                  (len, (maskL,
                          (maskR,
                            (result, (a1_map, (a2_dq, (tstp_dq, dn)))))))))),
      a)
    = (let (Some _, tssa) = safe_hd tss in
       let m = dq_nth a2_dq zero_nata in
       let i = args_ivl args in
       let t = dresult_maggauxa ag a result in
       let tssb = tl_queue tssa in
       let (ts, tssc) =
         (match safe_hd tssb with (None, tssc) -> (zero_nata, tssc)
           | (Some ts, tssc) -> (ts, tssc))
         in
       let (tablesa, taken) =
         takedropWhile_queue
           (fun (_, tstp) ->
             not (ts_tp_lt i ts (plus_nata (minus_nata tp len) one_nata) tstp))
           tables
         in
       let to_del_approx =
         sup_setb
           (finite_UNIV_list, cenum_list, (ceq_list ceq_event_data),
             (cproper_interval_list ccompare_event_data), set_impl_list)
           (set ((ceq_set
                   (cenum_list, (ceq_list ceq_event_data),
                     (cproper_interval_list
                       ccompare_event_data).ccompare_cproper_interval)),
                  (ccompare_set
                    (finite_UNIV_list, (ceq_list ceq_event_data),
                      (cproper_interval_list ccompare_event_data),
                      set_impl_list)),
                  set_impl_set)
             (mapa fst taken))
         in
       let to_del =
         edl_filter
           (fun x ->
             (match edl_lookup_tstp m x with None -> false
               | Some tstp ->
                 not (ts_tp_lt i ts (plus_nata (minus_nata tp len) one_nata)
                       tstp)))
           to_del_approx
         in
       let ma =
         mapping_delete_set
           (finite_UNIV_list, (ceq_list ceq_event_data),
             (ccompare_list ccompare_event_data), (equal_list equal_event_data))
           m to_del
         in
       let a2_dqa = dq_tl a2_dq in
       let maa = dq_nth a2_dqa zero_nata in
       let resulta =
         (if equal_nata len one_nata then edl_bot
           else edl_union (edl_minus result to_del) (unbox edl_keys_tstp_v maa))
         in
       let a2_dqb =
         dq_upd a2_dqa zero_nata
           (if equal_nata len one_nata then edl_mempty_tstp
             else combine (ccompare_list ccompare_event_data) max_tstp ma maa)
         in
       let tstp_dqa = dq_tl tstp_dq in
       let to_ins =
         unbox edl_mfilter_tstp_v (fun k _ -> is_none (edl_lookup_tstp ma k))
           maa
         in
       let aa =
         (if equal_nata len one_nata then dinit_maggauxa ag
           else dinsert_maggauxa ag (unbox edl_keys_tstp_v to_ins)
                  (ddelete_maggauxa ag to_del a))
         in
        ((tp, (tssc,
                (tablesa,
                  (minus_nata len one_nata,
                    (maskL,
                      (maskR,
                        (resulta,
                          (a1_map, (a2_dqb, (tstp_dqa, t :: dn)))))))))),
          aa));;

let rec gashift_dq
  args ag nt
    ((tp, (tss, (tables,
                  (len, (maskL,
                          (maskR,
                            (result, (a1_map, (a2_dq, (tstp_dq, dn)))))))))),
      a)
    = (let (tss_queue, tssa) =
         takeWhile_queue (fun t -> not (memR (args_ivl args) (minus_nata nt t)))
           tss
         in
        foldl (fun aux _ -> gaeval_step_dq args ag aux)
          ((tp, (tssa,
                  (tables,
                    (len, (maskL,
                            (maskR,
                              (result, (a1_map, (a2_dq, (tstp_dq, dn)))))))))),
            a)
          (linearize tss_queue));;

let rec gaadd_new_dq
  args ag msk rel1 rel2 nt aux =
    (let ((tp, (tss, (tables,
                       (len, (maskL,
                               (maskR,
                                 (result,
                                   (a1_map, (a2_dq, (tstp_dq, dn)))))))))),
           a)
       = gashift_dq args ag nt aux in
     let i = args_ivl args in
     let pos = args_pos args in
     let inz = memL i zero_nata in
     let new_tstp = (if inz then Inr tp else Inl nt) in
     let tstp_dqa = dq_push nt tstp_dq in
     let p =
       (fun t ->
         memL i
           (minus_nata nt (dq_nth tstp_dqa (minus_nata t (minus_nata tp len)))))
       in
     let (tbl, (a2_dqa, resulta)) =
       fold (de_guntil_elem_step_dq a1_map msk pos tp len inz p new_tstp)
         (csl (finite_UNIV_list, (ceq_list ceq_event_data),
                (ccompare_list ccompare_event_data))
           rel2)
         (edl_bot, (a2_dq, result))
       in
     let tablesa = append_queue (tbl, new_tstp) tables in
     let a2_dqb = dq_push edl_mempty_tstp a2_dqa in
     let a1_mapa =
       (if pos
         then unbox edl_mfilter_nat_v (fun asa _ -> edl_member asa rel1)
                (unbox edl_upd_set_nat_v a1_map (fun _ -> tp)
                  (edl_minus rel1 (unbox edl_keys_nat_v a1_map)))
         else unbox edl_upd_set_nat_v a1_map (fun _ -> tp) rel1)
       in
     let tssa = append_queue nt tss in
      ((plus_nata tp one_nata,
         (tssa,
           (tablesa,
             (plus_nata len one_nata,
               (maskL,
                 (maskR, (resulta, (a1_mapa, (a2_dqb, (tstp_dqa, dn)))))))))),
        dinsert_maggauxa ag (edl_minus resulta result) a));;

let rec add_new_u_d
  args msk rel1 rel2 nt x5 = match args, msk, rel1, rel2, nt, x5 with
    args, msk, rel1, rel2, nt, MUD_dns a ->
      (fun () -> (MUD_dns (de_gadd_new_dq args msk rel1 rel2 nt a)))
    | args, msk, rel1, rel2, nt, MUD_evt a ->
        (fun () -> (MUD_evt (de_gadd_new_evt args rel1 rel2 nt a)))
    | args, msk, rel1, rel2, nt, MUD_agg (ag, a) ->
        (fun () -> (MUD_agg (ag, gaadd_new_dq args ag msk rel1 rel2 nt a)));;

let rec uassign1 p t d = take p d @ umeval_trm t d :: drop p d;;

let rec uassign p t d = edl_image (uassign1 p t) d;;

let rec umtrm
  xa0 x = match xa0, x with MVar v, x -> edl_insert [x] edl_bot
    | MConst c, x ->
        (if equal_event_dataa c x then edl_insert [] edl_bot else edl_bot);;

let rec de_geval_evt
  args nt aux =
    (let (nts, (win, (rest, (len, (bend, (cnt, (cur, dn))))))) =
       de_gevt_shift args nt aux in
      (rev dn, (nts, (win, (rest, (len, (bend, (cnt, (cur, [])))))))));;

let rec de_geval_dq
  args nt aux =
    (let (tp, (tss, (tables,
                      (len, (maskL,
                              (maskR,
                                (result, (a1_map, (a2_dq, (tstp_dq, dn))))))))))
       = de_gshift_dq args nt aux in
      (rev dn,
        (tp, (tss, (tables,
                     (len, (maskL,
                             (maskR,
                               (result,
                                 (a1_map, (a2_dq, (tstp_dq, []))))))))))));;

let rec gaeval_dq
  args ag nt aux =
    (let ((tp, (tss, (tables,
                       (len, (maskL,
                               (maskR,
                                 (result,
                                   (a1_map, (a2_dq, (tstp_dq, dn)))))))))),
           a)
       = gashift_dq args ag nt aux in
      (rev dn,
        ((tp, (tss, (tables,
                      (len, (maskL,
                              (maskR,
                                (result,
                                  (a1_map, (a2_dq, (tstp_dq, [])))))))))),
          a)));;

let rec eval_u_d
  args nt x2 = match args, nt, x2 with
    args, nt, MUD_dns a ->
      (fun () -> (let (zs, aa) = de_geval_dq args nt a in (zs, MUD_dns aa)))
    | args, nt, MUD_evt a ->
        (fun () -> (let (zs, aa) = de_geval_evt args nt a in (zs, MUD_evt aa)))
    | args, nt, MUD_agg (ag, a) ->
        (fun () ->
          (let (zs, aa) = gaeval_dq args ag nt a in (zs, MUD_agg (ag, aa))));;

let rec hmap
  f x1 = match f, x1 with f, [] -> (fun () -> [])
    | f, x :: xs ->
        binda (f x)
          (fun y -> binda (hmap f xs) (fun ys -> (fun () -> (y :: ys))));;

let rec deval_step
  rc j ts db x4 = match rc, j, ts, db, x4 with
    rc, j, ts, db, DAnds (ps, ns, l, buf) ->
      binda (hmap (rc j ts db) l)
        (fun r ->
          binda (mebufn_take_j (dmulti_join ps ns) mbuf_t_empty
                  (umebufn_add (mapa fst r) buf))
            (fun p ->
              (fun () ->
                (rep_mbuf_t (fst p), DAnds (ps, ns, mapa snd r, snd p)))))
    | rc, j, ts, db, DFail ->
        failwith "deval: the formula is outside the dense fragment"
    | rc, j, ts, db, DRel rel ->
        (fun () -> (replicate (size_lista ts) rel, DRel rel))
    | rc, j, ts, db, DPredS (e, ar) ->
        (fun () ->
          ((match
             lookupa
               ((ccompare_prod ccompare_string8 ccompare_nat),
                 (equal_prod equal_string8 equal_nat))
               db (e, ar)
             with None -> replicate (size_lista ts) edl_bot | Some xs -> xs),
            DPredS (e, ar)))
    | rc, j, ts, db, DPredM (e, ar, tms, cs) ->
        (fun () ->
          ((match
             lookupa
               ((ccompare_prod ccompare_string8 ccompare_nat),
                 (equal_prod equal_string8 equal_nat))
               db (e, ar)
             with None -> replicate (size_lista ts) edl_bot
             | Some a -> mapa (umatch_table tms cs) a),
            DPredM (e, ar, tms, cs)))
    | rc, j, ts, db, DAnd (pl, phi, pos, psi, buf) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            binda (rc j ts db psi)
              (fun (ys, psia) ->
                binda (mebuf2_take_j (fun r1 -> dbin_join_h pl r1 pos)
                        (mebuf2_add xs ys buf))
                  (fun r ->
                    (fun () -> (fst r, DAnd (pl, phia, pos, psia, snd r))))))
    | rc, j, ts, db, DAndRel (phi, conf) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            (fun () ->
              (mapa (edl_filter (ueval_constraint conf)) xs,
                DAndRel (phia, conf))))
    | rc, j, ts, db, DOr (phi, psi, buf) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            binda (rc j ts db psi)
              (fun (ys, psia) ->
                (fun () ->
                  (let (zs, bufa) =
                     mebuf2_take
                       (sup_seta
                         ((ceq_list ceq_event_data),
                           (ccompare_list ccompare_event_data)))
                       (mebuf2_add xs ys buf)
                     in
                    (zs, DOr (phia, psia, bufa))))))
    | rc, j, ts, db, DNeg phi ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            (fun () ->
              (mapa (fun r ->
                      (if unbox edl_set_eq_v r edl_bot
                        then edl_insert [] edl_bot else edl_bot))
                 xs,
                DNeg phia)))
    | rc, j, ts, db, DExists (phi, drop0) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            (fun () ->
              ((if drop0 then mapa (edl_image tla) xs else xs),
                DExists (phia, drop0))))
    | rc, j, ts, db, DAgg (g0, omega, f, k, pos, phi) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            (fun () ->
              (mapa (uagg g0 omega f k pos) xs,
                DAgg (g0, omega, f, k, pos, phia))))
    | rc, j, ts, db, DPrev (i, phi, first, buf, nts) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            (fun () ->
              (if first && null ts
                then ([], DPrev (i, phia, true, mbuf_t_append buf xs,
                                  mbuf_t_append nts ts))
                else (let (zs, (bufa, ntsa)) =
                        umeprev_next i (mbuf_t_append buf xs)
                          (mbuf_t_append nts ts)
                        in
                       ((if first then edl_bot :: zs else zs),
                         DPrev (i, phia, false, bufa, ntsa))))))
    | rc, j, ts, db, DNext (i, phi, first, nts) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            (fun () ->
              (let (xsa, firsta) =
                 (match (xs, first) with ([], b) -> ([], b)
                   | (_ :: xsa, true) -> (xsa, false)
                   | (x :: xsa, false) -> (x :: xsa, false))
                 in
               let (zs, (_, ntsa)) =
                 umeprev_next i (mbuf_t_append mbuf_t_empty xsa)
                   (mbuf_t_append nts ts)
                 in
                (zs, DNext (i, phia, firsta, ntsa)))))
    | rc, j, ts, db, DSince (args, phi, psi, buf, aux) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            binda (rc j ts db psi)
              (fun (ys, psia) ->
                binda (eval_since_d args [] (umebuf2S_add xs ys ts buf) aux)
                  (fun (zs, (bufa, auxa)) ->
                    (fun () -> (zs, DSince (args, phia, psia, bufa, auxa))))))
    | rc, j, ts, db, DUntil (args, msk, phi, psi, buf, nts, t, aux) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            binda (rc j ts db psi)
              (fun (ys, psia) ->
                binda (mebuf2t_take_j (add_new_u_d args msk) aux
                        (mebuf2_add xs ys buf) t (mbuf_t_append nts ts))
                  (fun (auxa, (bufa, (nt, ntsa))) ->
                    binda (eval_u_d args nt auxa)
                      (fun z ->
                        (fun () ->
                          (fst z,
                            DUntil
                              (args, msk, phia, psia, bufa, ntsa, nt,
                                snd z)))))))
    | rc, j, ts, db, DAndAssign (p, t, phi) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            (fun () -> (mapa (uassign p t) xs, DAndAssign (p, t, phia))))
    | rc, j, ts, db, DTP (mt, i) ->
        (fun () ->
          (mapa (fun x -> umtrm mt (EInt (integer_of_nat x))) (upt i j),
            DTP (mt, j)))
    | rc, j, ts, db, DTS mt ->
        (fun () ->
          (mapa (fun x -> umtrm mt (EInt (integer_of_nat x))) ts, DTS mt))
    | rc, j, ts, db, DLet (p, m, phi, psi) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            binda (rc j ts
                     (updateb
                       ((ccompare_prod ccompare_string8 ccompare_nat),
                         (equal_prod equal_string8 equal_nat))
                       (p, m) xs db)
                    psi)
              (fun (ys, psia) -> (fun () -> (ys, DLet (p, m, phia, psia)))))
    | rc, j, ts, db, DMatchP (i, mr, mrs, msks, phi_s, buf, nts, aux) ->
        binda (hmap (rc j ts db) phi_s)
          (fun r ->
            (fun () ->
              (let (a, b) =
                 umebufnt_take
                   (fun rels t (zs, ax) ->
                     (let (z, a) = de_gupdate_matchP msks i mr mrs rels t ax in
                       (mbuf_t_append zs [z], a)))
                   (mbuf_t_empty, aux) (umebufn_add (mapa fst r) buf) zero_nata
                   (mbuf_t_append nts ts)
                 in
                (let (zs, auxa) = a in
                  (fun (bufa, (_, ntsa)) ->
                    (rep_mbuf_t zs,
                      DMatchP
                        (i, mr, mrs, msks, mapa snd r, bufa, ntsa, auxa))))
                  b)))
    | rc, j, ts, db, DMatchF (i, mr, mrs, msks, phi_s, buf, nts, t, aux) ->
        binda (hmap (rc j ts db) phi_s)
          (fun r ->
            (fun () ->
              (let (auxa, (bufa, (nt, ntsa))) =
                 umebufnt_take (de_gupdate_matchF msks i mr mrs) aux
                   (umebufn_add (mapa fst r) buf) t (mbuf_t_append nts ts)
                 in
               let (zs, auxb) = de_geval_matchF i mr nt auxa in
                (zs, DMatchF
                       (i, mr, mrs, msks, mapa snd r, bufa, ntsa, nt, auxb)))))
    | rc, j, ts, db, DTrigger (dags, phi, psi, dbuf, nts, daux) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            binda (rc j ts db psi)
              (fun (ys, psia) ->
                (fun () ->
                  (let (a, b) =
                     umebuf2T_take
                       (fun r1 r2 t (zs, ax) ->
                         (let axa = de_gupdate_mmtaux dags t r1 r2 ax in
                           (zs @ [de_gresult_mmtaux dags axa], axa)))
                       ([], daux) (mebuf2_add xs ys dbuf) (mbuf_t_append nts ts)
                     in
                    (let (zs, dauxa) = a in
                      (fun (dbufa, ntsa) ->
                        (zs, DTrigger (dags, phia, psia, dbufa, ntsa, dauxa))))
                      b))))
    | rc, j, ts, db,
        DAndTrigger (pl, phia, buf1, dags, phi, psi, buf2, nts, daux)
        -> binda (rc j ts db phia)
             (fun (asa, phiaa) ->
               binda (rc j ts db phi)
                 (fun (xs, phib) ->
                   binda (rc j ts db psi)
                     (fun (ys, psia) ->
                       binda (fun () ->
                               (umebuf2T_take
                                 (fun r1 r2 t (zs, ax) ->
                                   (let axa = de_gupdate_mmtaux dags t r1 r2 ax
                                      in
                                     (zs @
[(if de_gmmtaux_empty axa then None else Some (de_gresult_mmtaux dags axa))],
                                       axa)))
                                 ([], daux) (mebuf2_add xs ys buf2)
                                 (mbuf_t_append nts ts)))
                         (fun (a, b) ->
                           (let (zs_trigger, dauxa) = a in
                             (fun (buf2a, ntsa) ->
                               binda (mebuf2_take_j
                                       (fun r1 aa ->
 (match aa with None -> (fun () -> r1)
   | Some z ->
     (match r1 with None -> (fun () -> None)
       | Some ab ->
         binda (dbin_join_h pl ab true z) (fun c -> (fun () -> (Some c))))))
                                       (mebuf2_add
 (mapa (fun aa -> Some aa) asa) zs_trigger buf1))
                                 (fun r ->
                                   (fun () ->
                                     (mapa the (fst r),
                                       DAndTrigger
 (pl, phiaa, snd r, dags, phib, psia, buf2a, ntsa, dauxa))))))
                             b))))
    | rc, j, ts, db, DLetPast (p, m, phi, psi, i, buf) ->
        binda (letpast_meval0_h (rc j) j i [] (list_of_option buf) (p, m) ts db
                phi)
          (fun (xs, (ia, (bufa, phia))) ->
            binda (rc j ts
                     (updateb
                       ((ccompare_prod ccompare_string8 ccompare_nat),
                         (equal_prod equal_string8 equal_nat))
                       (p, m) xs db)
                    psi)
              (fun (ys, psia) ->
                (fun () -> (ys, DLetPast (p, m, phia, psia, ia, bufa)))))
    | rc, j, ts, db, DFrz (p, m, phi, psi, jfrz, jpsi0, jphi, alpha_s) ->
        binda (rc j ts db phi)
          (fun (xs, phia) ->
            binda (rc j ts
                     (updateb
                       ((ccompare_prod ccompare_string8 ccompare_nat),
                         (equal_prod equal_string8 equal_nat))
                       (p, m) [] db)
                    psi)
              (fun (zs0, psia) ->
                (let zs0_out = drop (minus_nata jfrz jpsi0) zs0 in
                 let jpsi0a = plus_nata jpsi0 (size_lista zs0) in
                 let alpha_sa =
                   drop (plus_nata (minus_nata jfrz jphi) (size_lista zs0_out))
                     (alpha_s @ xs)
                   in
                  binda (freeze_meval0_h
                          (fun alpha ->
                            rc j []
                              (updateb
                                ((ccompare_prod ccompare_string8 ccompare_nat),
                                  (equal_prod equal_string8 equal_nat))
                                (p, m) (replicate j alpha)
                                (map_values
                                  (ccompare_prod ccompare_string8 ccompare_nat)
                                  (fun _ _ -> []) db))
                              psia)
                          (minus_nata jfrz jpsi0a) alpha_sa)
                    (fun r ->
                      (fun () ->
                        (zs0_out @ fst r,
                          DFrz (p, m, phia, psia,
                                 plus_nata (plus_nata jfrz (size_lista zs0_out))
                                   (size_lista (fst r)),
                                 jpsi0a, plus_nata jphi (size_lista xs),
                                 snd r)))))));;

let rec deval j ts db phi_0 = deval_step deval j ts db phi_0;;

let rec args_agg
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_agg;;

let rec aggargs_y
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_y;;

let rec aggargs_tys
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_tys;;

let rec aggargs_cols
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_cols;;

let rec dagg_child_cols args = set_cols (aggargs_cols args);;

let rec dagg_group_cols
  args =
    mapa (fun c -> minus_nata c (size_lista (aggargs_tys args)))
      (drop (size_lista (aggargs_tys args)) (dagg_child_cols args));;

let rec merge_cols
  x0 ds = match x0, ds with [], ds -> ds
    | c :: cs, [] -> c :: merge_cols cs []
    | c :: cs, d :: ds ->
        (if less_nat c d then c :: merge_cols cs (d :: ds)
          else (if less_nat d c then d :: merge_cols (c :: cs) ds
                 else c :: merge_cols cs ds));;

let rec dagg_cols args = merge_cols (dagg_group_cols args) [aggargs_y args];;

let rec trm_vars = function Var x -> [x]
                   | Const c -> []
                   | Plus (a, b) -> trm_vars a @ trm_vars b
                   | Minus (a, b) -> trm_vars a @ trm_vars b
                   | UMinus a -> trm_vars a
                   | Mult (a, b) -> trm_vars a @ trm_vars b
                   | Div (a, b) -> trm_vars a @ trm_vars b
                   | Mod (a, b) -> trm_vars a @ trm_vars b
                   | F2i a -> trm_vars a
                   | I2f a -> trm_vars a;;

let rec tms_cols
  tms = csorted_list_of_set (ceq_nat, ccompare_nat)
          (set (ceq_nat, ccompare_nat, set_impl_nat) (maps trm_vars tms));;

let rec mtrm_dcols mt = (match mt with MVar v -> [v] | MConst _ -> []);;

let rec dands_cols acc x1 = match acc, x1 with acc, [] -> acc
                     | acc, c :: cs -> dands_cols (merge_cols acc c) cs;;

let rec mcols
  n x1 = match n, x1 with n, MPred (e, tms, mode) -> Some (tms_cols tms)
    | n, MAnd (a, phi, pos, b, psi, buf) ->
        Some (if pos then merge_cols (set_cols a) (set_cols b) else set_cols a)
    | n, MAnds (a_pos, a_neg, l, buf) ->
        (match a_pos with [] -> None
          | a :: asa -> Some (dands_cols (set_cols a) (mapa set_cols asa)))
    | n, MAgg (args, phi) -> Some (dagg_cols args)
    | n, MAndRel (phi, conf) -> mcols n phi
    | n, MOr (phi, psi, buf) -> mcols n phi
    | n, MNeg phi -> Some []
    | n, MExists phi ->
        (match mcols (suc n) phi with None -> None
          | Some cs ->
            Some (map_filter
                   (fun x ->
                     (if not (equal_nata x zero_nata)
                       then Some (minus_nata x one_nata) else None))
                   cs))
    | n, MPrev (i, phi, first, buf, nts) -> mcols n phi
    | n, MNext (i, phi, first, nts) -> mcols n phi
    | n, MSince (args, phi, psi, buf, aux) ->
        (match args_agg args with None -> Some (set_cols (args_R args))
          | Some aggargs -> Some (dagg_cols aggargs))
    | n, MUntil (args, phi, psi, buf, nts, t, aux) ->
        (match args_agg args with None -> Some (set_cols (args_R args))
          | Some aggargs -> Some (dagg_cols aggargs))
    | n, MTrigger (args, phi, psi, buf, nts, aux) ->
        Some (set_cols (args_R args))
    | n, MAndTrigger (v, phia, buf1, args, phi, psi, buf2, nts, aux) ->
        Some (merge_cols (set_cols v) (set_cols (args_R args)))
    | n, MFrz (p, m, phi, psi, jfrz, jpsi0, jphi, alpha_s) -> mcols n psi
    | n, MLetPast (p, m, phi, psi, i, buf) -> mcols n psi
    | n, MMatchP (i, mr, mrs, phi_s, buf, nts, aux) ->
        map_option (fun css -> fold merge_cols css [])
          (those (mapa (mcols n) phi_s))
    | n, MMatchF (i, mr, mrs, phi_s, buf, nts, t, aux) ->
        map_option (fun css -> fold merge_cols css [])
          (those (mapa (mcols n) phi_s))
    | n, MAndAssign (phi, conf) ->
        (match mcols n phi with None -> None
          | Some cs ->
            (if membera equal_nat cs (fst conf) ||
                  not (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                        (fvi_trm zero_nata (snd conf))
                        (set (ceq_nat, ccompare_nat, set_impl_nat) cs))
              then None else Some (merge_cols cs [fst conf])))
    | n, MLet (p, m, phi, psi) -> mcols n psi
    | n, MTP (mt, i) -> Some (mtrm_dcols mt)
    | n, MTS mt -> Some (mtrm_dcols mt)
    | n, MRel v -> None;;

let rec sorted_wrt p x1 = match p, x1 with p, [] -> true
                     | p, x :: ys -> list_all (p x) ys && sorted_wrt p ys;;

let rec special_args
  args =
    is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) (args_L args) ||
      set_eq (cenum_nat, ceq_nat, ccompare_nat) (args_L args) (args_R args);;

let rec de_ginit_msaux
  args msk =
    (zero_nata,
      (zero_nata,
        (msk, (empty_queue,
                (empty_queue,
                  (edl_bot,
                    (edl_mempty_table,
                      (edl_mempty_nat,
                        (edl_mempty_table, edl_mempty_nat)))))))));;

let rec de_ginit_sevt
  args = (zero_nata, (empty_queue, (empty_queue, (edl_mempty_nat, edl_bot))));;

let rec dainit_msaux
  args ag msk = (de_ginit_msaux args msk, dinit_maggauxa ag);;

let rec join_mask
  n x = mapa (fun i -> member (ceq_nat, ccompare_nat) i x) (upt zero_nata n);;

let rec args_n
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_n;;

let rec hsd_init2
  args =
    binda (im_new (heap_list heap_event_data) heap_nat (Z.of_int 16))
      (fun hin ->
        binda (im_new (heap_list heap_event_data) heap_nat (Z.of_int 16))
          (fun hsince ->
            (fun () ->
              ((zero_nata,
                 (zero_nata,
                   (join_mask (args_n args) (args_L args),
                     (join_mask (args_n args) (args_R args),
                       (empty_queue, (empty_queue, edl_bot)))))),
                (hin, hsince)))));;

let rec sevt_applies
  args =
    is_none (args_agg args) &&
      is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) (args_L args);;

let rec init_d
  hp ago args msk =
    (match ago
      with None ->
        (if sevt_applies args then (fun () -> (MSD_evt (de_ginit_sevt args)))
          else (if hp && (is_none (args_agg args) && special_args args)
                 then binda (hsd_init2 args) (fun q -> (fun () -> (MSD_imp q)))
                 else (fun () -> (MSD_dns (de_ginit_msaux args msk)))))
      | Some ag -> (fun () -> (MSD_agg (ag, dainit_msaux args ag msk))));;

let rec bounded x = snd (snd (rep_I x));;

let rec atms (_A1, _A2, _A3)
  = function Skip x1 -> bot_set (_A1, _A2, _A3)
    | Test x2 -> insert (_A1, _A2) x2 (bot_set (_A1, _A2, _A3))
    | Plusa (x31, x32) ->
        sup_seta (_A1, _A2) (atms (_A1, _A2, _A3) x31)
          (atms (_A1, _A2, _A3) x32)
    | Times (x41, x42) ->
        sup_seta (_A1, _A2) (atms (_A1, _A2, _A3) x41)
          (atms (_A1, _A2, _A3) x42)
    | Star x5 -> atms (_A1, _A2, _A3) x5;;

let rec equal_safety x0 x1 = match x0, x1 with Strict, Lax -> false
                       | Lax, Strict -> false
                       | Lax, Lax -> true
                       | Strict, Strict -> true;;

let rec safe_regex (_B1, _B2, _B3, _B4, _B5)
  fv safe m uu x4 = match fv, safe, m, uu, x4 with
    fv, safe, m, uu, Skip n -> true
    | fv, safe, m, g, Test phi -> safe g phi
    | fv, safe, m, g, Plusa (r, s) ->
        (equal_safety g Lax ||
          set_eq (_B2, _B3, _B4.ccompare_cproper_interval)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv s)) &&
          (safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe m g r &&
            safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe m g s)
    | fv, safe, Futu, g, Times (r, s) ->
        (equal_safety g Lax ||
          less_eq_set (_B2, _B3, _B4.ccompare_cproper_interval)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv s)) &&
          (safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Futu g s &&
            safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Futu Lax r)
    | fv, safe, Past, g, Times (r, s) ->
        (equal_safety g Lax ||
          less_eq_set (_B2, _B3, _B4.ccompare_cproper_interval)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv s)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)) &&
          (safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Past g r &&
            safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Past Lax s)
    | fv, safe, m, g, Star r ->
        (equal_safety g Lax ||
          is_empty (_B1, _B3, _B4)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)) &&
          safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe m g r;;

let rec safe_dual
  conjoined safety_pred phi i psi =
    (if memL i zero_nata && memR i zero_nata
      then safety_pred psi &&
             (less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
                (fvi zero_nata psi) &&
               (safety_pred phi ||
                 (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                   | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                   | Eq (_, _) -> false | Less (_, _) -> false
                   | LessEq (_, _) -> false | Neg a -> safety_pred a
                   | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                   | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                   | Prev (_, _) -> false | Next (_, _) -> false
                   | Since (_, _, _) -> false | Until (_, _, _) -> false
                   | Trigger (_, _, _) -> false | Release (_, _, _) -> false
                   | MatchF (_, _) -> false | MatchP (_, _) -> false
                   | TP _ -> false | TS _ -> false)))
      else conjoined &&
             (safety_pred phi &&
               (safety_pred psi &&
                 set_eq (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
                   (fvi zero_nata psi))));;

let rec dands_plans
  acc x1 = match acc, x1 with acc, [] -> []
    | acc, c :: cs -> mk_djoin acc c :: dands_plans (merge_cols acc c) cs;;

let rec reindex_trm
  cs x1 = match cs, x1 with cs, Var x -> Var (col_pos cs x)
    | cs, Const c -> Const c
    | cs, Plus (a, b) -> Plus (reindex_trm cs a, reindex_trm cs b)
    | cs, Minus (a, b) -> Minus (reindex_trm cs a, reindex_trm cs b)
    | cs, UMinus a -> UMinus (reindex_trm cs a)
    | cs, Mult (a, b) -> Mult (reindex_trm cs a, reindex_trm cs b)
    | cs, Div (a, b) -> Div (reindex_trm cs a, reindex_trm cs b)
    | cs, Mod (a, b) -> Mod (reindex_trm cs a, reindex_trm cs b)
    | cs, F2i a -> F2i (reindex_trm cs a)
    | cs, I2f a -> I2f (reindex_trm cs a);;

let rec aggargs_omega
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_omega;;

let rec aggargs_g0
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_g0;;

let rec aggargs_f
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_f;;

let rec dagg_pos
  args =
    size_lista
      (filtera (fun c -> less_nat c (aggargs_y args)) (dagg_group_cols args));;

let rec dagg_of
  ag = Daggargs_ext
         (aggargs_g0 ag, aggargs_omega ag,
           reindex_trm (dagg_child_cols ag) (aggargs_f ag),
           size_lista (aggargs_tys ag), dagg_pos ag, ());;

let rec dunfuse
  args =
    init_args (args_ivl args) (args_n args) (args_L args) (args_R args)
      (args_pos args) None;;

let rec annotate_verdicts_j
  i tq x2 acc = match i, tq, x2, acc with i, tq, [], acc -> (i, (tq, rev acc))
    | i, tq, v :: vs, acc ->
        (match pop tq
          with (None, tqa) ->
            (plus_nata (plus_nata i one_nata) (size_lista vs),
              (funpow (plus_nata one_nata (size_lista vs)) tl_queue tqa,
                rev acc))
          | (Some t, tqa) ->
            annotate_verdicts_j (plus_nata i one_nata) tqa vs
              ((i, (t, v)) :: acc));;

let rec mstep_d
  tdb sti =
    (let (i, (j, (m, (n, tq)))) = sti in
      binda (deval (plus_nata j one_nata) [snd tdb] (fst tdb) m)
        (fun (vs, ma) ->
          (fun () ->
            (let (ia, (tqa, vsa)) =
               annotate_verdicts_j i (append_queue (snd tdb) tq) vs [] in
              (vsa, (ia, (plus_nata j one_nata, (ma, (n, tqa)))))))));;

let rec flip_int
  xa = Abs_I (if bounded xa
               then ((fun i -> not (memR xa i)), ((fun _ -> true), false))
               else ((fun _ -> true), ((fun _ -> true), false)));;

let rec less_eq_enat q x1 = match q, x1 with Enat m, Enat n -> less_eq_nat m n
                       | q, Infinity_enat -> true
                       | Infinity_enat, Enat n -> false;;

let rec interval
  xb xc =
    Abs_I (if less_eq_enat (Enat xb) xc
            then (less_eq_nat xb,
                   ((fun i -> less_eq_enat (Enat i) xc),
                     not (equal_enat xc Infinity_enat)))
            else ((fun _ -> true), ((fun _ -> true), false)));;

let rec meval_trm
  x0 v = match x0, v with Var x, v -> the (nth v x)
    | Const x, v -> x
    | Plus (x, y), v -> plus_event_data (meval_trm x v) (meval_trm y v)
    | Minus (x, y), v -> minus_event_data (meval_trm x v) (meval_trm y v)
    | UMinus x, v -> uminus_event_data (meval_trm x v)
    | Mult (x, y), v -> times_event_data (meval_trm x v) (meval_trm y v)
    | Div (x, y), v -> divide_event_data (meval_trm x v) (meval_trm y v)
    | Mod (x, y), v -> modulo_event_data (meval_trm x v) (meval_trm y v)
    | F2i x, v -> EInt (integer_of_event_data (meval_trm x v))
    | I2f x, v -> EFloat (double_of_event_data (meval_trm x v));;

let rec less_eq_rec_safety x0 uu = match x0, uu with Unused, uu -> true
                             | PastRec, PastRec -> true
                             | PastRec, NonFutuRec -> true
                             | PastRec, AnyRec -> true
                             | NonFutuRec, NonFutuRec -> true
                             | NonFutuRec, AnyRec -> true
                             | AnyRec, AnyRec -> true
                             | PastRec, Unused -> false
                             | NonFutuRec, Unused -> false
                             | NonFutuRec, PastRec -> false
                             | AnyRec, Unused -> false
                             | AnyRec, PastRec -> false
                             | AnyRec, NonFutuRec -> false;;

let rec int_remove_lower_bound
  xa = Abs_I ((fun _ -> true), (memR xa, bounded xa));;

let rec eventually i phi = Until (tt, i, phi);;

let rec always_safe_bounded
  i phi =
    And (eventually i phi,
          Neg (eventually i
                (And (Or (once (int_remove_lower_bound i) phi,
                           eventually (int_remove_lower_bound i) phi),
                       Neg phi))));;

let rec release_safe_bounded
  phi i psi =
    And (eventually i tt,
          Or (Or (always_safe_bounded i psi,
                   eventually (flip_int_less_lower i) phi),
               eventually (flip_int_less_lower i)
                 (Next (all, Until (psi, int_remove_lower_bound i,
                                     And (psi, phi))))));;

let rec and_release_safe_bounded
  phia phi i psi =
    Or (And (phia, Neg (eventually i tt)),
         And (phia, release_safe_bounded phi i psi));;

let rec safe_assignment
  x alpha =
    (match alpha with Pred (_, _) -> false | Let (_, _, _) -> false
      | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
      | Eq (Var xa, Var y) ->
        equal_boola (not (member (ceq_nat, ccompare_nat) xa x))
          (member (ceq_nat, ccompare_nat) y x)
      | Eq (Var xa, Const event_data) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Const event_data)) x
      | Eq (Var xa, Plus (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Plus (trm1, trm2))) x
      | Eq (Var xa, Minus (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Minus (trm1, trm2))) x
      | Eq (Var xa, UMinus trm) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (UMinus trm)) x
      | Eq (Var xa, Mult (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mult (trm1, trm2))) x
      | Eq (Var xa, Div (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Div (trm1, trm2))) x
      | Eq (Var xa, Mod (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mod (trm1, trm2))) x
      | Eq (Var xa, F2i trm) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (F2i trm)) x
      | Eq (Var xa, I2f trm) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (I2f trm)) x
      | Eq (Const event_data, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Const event_data)) x
      | Eq (Const _, Const _) -> false | Eq (Const _, Plus (_, _)) -> false
      | Eq (Const _, Minus (_, _)) -> false | Eq (Const _, UMinus _) -> false
      | Eq (Const _, Mult (_, _)) -> false | Eq (Const _, Div (_, _)) -> false
      | Eq (Const _, Mod (_, _)) -> false | Eq (Const _, F2i _) -> false
      | Eq (Const _, I2f _) -> false
      | Eq (Plus (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Plus (trm1, trm2))) x
      | Eq (Plus (_, _), Const _) -> false
      | Eq (Plus (_, _), Plus (_, _)) -> false
      | Eq (Plus (_, _), Minus (_, _)) -> false
      | Eq (Plus (_, _), UMinus _) -> false
      | Eq (Plus (_, _), Mult (_, _)) -> false
      | Eq (Plus (_, _), Div (_, _)) -> false
      | Eq (Plus (_, _), Mod (_, _)) -> false | Eq (Plus (_, _), F2i _) -> false
      | Eq (Plus (_, _), I2f _) -> false
      | Eq (Minus (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Minus (trm1, trm2))) x
      | Eq (Minus (_, _), Const _) -> false
      | Eq (Minus (_, _), Plus (_, _)) -> false
      | Eq (Minus (_, _), Minus (_, _)) -> false
      | Eq (Minus (_, _), UMinus _) -> false
      | Eq (Minus (_, _), Mult (_, _)) -> false
      | Eq (Minus (_, _), Div (_, _)) -> false
      | Eq (Minus (_, _), Mod (_, _)) -> false
      | Eq (Minus (_, _), F2i _) -> false | Eq (Minus (_, _), I2f _) -> false
      | Eq (UMinus trm, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (UMinus trm)) x
      | Eq (UMinus _, Const _) -> false | Eq (UMinus _, Plus (_, _)) -> false
      | Eq (UMinus _, Minus (_, _)) -> false | Eq (UMinus _, UMinus _) -> false
      | Eq (UMinus _, Mult (_, _)) -> false | Eq (UMinus _, Div (_, _)) -> false
      | Eq (UMinus _, Mod (_, _)) -> false | Eq (UMinus _, F2i _) -> false
      | Eq (UMinus _, I2f _) -> false
      | Eq (Mult (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mult (trm1, trm2))) x
      | Eq (Mult (_, _), Const _) -> false
      | Eq (Mult (_, _), Plus (_, _)) -> false
      | Eq (Mult (_, _), Minus (_, _)) -> false
      | Eq (Mult (_, _), UMinus _) -> false
      | Eq (Mult (_, _), Mult (_, _)) -> false
      | Eq (Mult (_, _), Div (_, _)) -> false
      | Eq (Mult (_, _), Mod (_, _)) -> false | Eq (Mult (_, _), F2i _) -> false
      | Eq (Mult (_, _), I2f _) -> false
      | Eq (Div (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Div (trm1, trm2))) x
      | Eq (Div (_, _), Const _) -> false
      | Eq (Div (_, _), Plus (_, _)) -> false
      | Eq (Div (_, _), Minus (_, _)) -> false
      | Eq (Div (_, _), UMinus _) -> false
      | Eq (Div (_, _), Mult (_, _)) -> false
      | Eq (Div (_, _), Div (_, _)) -> false
      | Eq (Div (_, _), Mod (_, _)) -> false | Eq (Div (_, _), F2i _) -> false
      | Eq (Div (_, _), I2f _) -> false
      | Eq (Mod (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mod (trm1, trm2))) x
      | Eq (Mod (_, _), Const _) -> false
      | Eq (Mod (_, _), Plus (_, _)) -> false
      | Eq (Mod (_, _), Minus (_, _)) -> false
      | Eq (Mod (_, _), UMinus _) -> false
      | Eq (Mod (_, _), Mult (_, _)) -> false
      | Eq (Mod (_, _), Div (_, _)) -> false
      | Eq (Mod (_, _), Mod (_, _)) -> false | Eq (Mod (_, _), F2i _) -> false
      | Eq (Mod (_, _), I2f _) -> false
      | Eq (F2i trm, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (F2i trm)) x
      | Eq (F2i _, Const _) -> false | Eq (F2i _, Plus (_, _)) -> false
      | Eq (F2i _, Minus (_, _)) -> false | Eq (F2i _, UMinus _) -> false
      | Eq (F2i _, Mult (_, _)) -> false | Eq (F2i _, Div (_, _)) -> false
      | Eq (F2i _, Mod (_, _)) -> false | Eq (F2i _, F2i _) -> false
      | Eq (F2i _, I2f _) -> false
      | Eq (I2f trm, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (I2f trm)) x
      | Eq (I2f _, Const _) -> false | Eq (I2f _, Plus (_, _)) -> false
      | Eq (I2f _, Minus (_, _)) -> false | Eq (I2f _, UMinus _) -> false
      | Eq (I2f _, Mult (_, _)) -> false | Eq (I2f _, Div (_, _)) -> false
      | Eq (I2f _, Mod (_, _)) -> false | Eq (I2f _, F2i _) -> false
      | Eq (I2f _, I2f _) -> false | Less (_, _) -> false
      | LessEq (_, _) -> false | Neg _ -> false | Or (_, _) -> false
      | And (_, _) -> false | Ands _ -> false | Exists (_, _) -> false
      | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
      | Next (_, _) -> false | Since (_, _, _) -> false
      | Until (_, _, _) -> false | Trigger (_, _, _) -> false
      | Release (_, _, _) -> false | MatchF (_, _) -> false
      | MatchP (_, _) -> false | TP _ -> false | TS _ -> false);;

let rec flip_int_double_upper
  xa = Abs_I (if bounded xa
               then ((fun i -> not (memR xa i)),
                      ((fun i ->
                         memR xa (divide_nata i (nat_of_integer (Z.of_int 2)))),
                        true))
               else ((fun _ -> true), ((fun _ -> true), false)));;

let rec always_safe_0
  i phi =
    Or (Until (phi, flip_int_double_upper i, Prev (all, phi)),
         Until (phi, i, And (phi, Next (flip_int i, tt))));;

let rec release_safe_0
  phi i psi = Or (Until (psi, i, And (psi, phi)), always_safe_0 i psi);;

let rec is_constraint = function Eq (t1, t2) -> true
                        | Less (t1, t2) -> true
                        | LessEq (t1, t2) -> true
                        | Neg (Eq (t1, t2)) -> true
                        | Neg (Less (t1, t2)) -> true
                        | Neg (LessEq (t1, t2)) -> true
                        | Pred (v, va) -> false
                        | Let (v, va, vb) -> false
                        | Frz (v, va, vb) -> false
                        | LetPast (v, va, vb) -> false
                        | Neg (Pred (va, vb)) -> false
                        | Neg (Let (va, vb, vc)) -> false
                        | Neg (Frz (va, vb, vc)) -> false
                        | Neg (LetPast (va, vb, vc)) -> false
                        | Neg (Neg va) -> false
                        | Neg (Or (va, vb)) -> false
                        | Neg (And (va, vb)) -> false
                        | Neg (Ands va) -> false
                        | Neg (Exists (va, vb)) -> false
                        | Neg (Agg (va, vb, vc, vd, ve)) -> false
                        | Neg (Prev (va, vb)) -> false
                        | Neg (Next (va, vb)) -> false
                        | Neg (Since (va, vb, vc)) -> false
                        | Neg (Until (va, vb, vc)) -> false
                        | Neg (Trigger (va, vb, vc)) -> false
                        | Neg (Release (va, vb, vc)) -> false
                        | Neg (MatchF (va, vb)) -> false
                        | Neg (MatchP (va, vb)) -> false
                        | Neg (TP va) -> false
                        | Neg (TS va) -> false
                        | Or (v, va) -> false
                        | And (v, va) -> false
                        | Ands v -> false
                        | Exists (v, va) -> false
                        | Agg (v, va, vb, vc, vd) -> false
                        | Prev (v, va) -> false
                        | Next (v, va) -> false
                        | Since (v, va, vb) -> false
                        | Until (v, va, vb) -> false
                        | Trigger (v, va, vb) -> false
                        | Release (v, va, vb) -> false
                        | MatchF (v, va) -> false
                        | MatchP (v, va) -> false
                        | TP v -> false
                        | TS v -> false;;

let rec is_Const = function Var x1 -> false
                   | Const x2 -> true
                   | Plus (x31, x32) -> false
                   | Minus (x41, x42) -> false
                   | UMinus x5 -> false
                   | Mult (x61, x62) -> false
                   | Div (x71, x72) -> false
                   | Mod (x81, x82) -> false
                   | F2i x9 -> false
                   | I2f x10 -> false;;

let rec times_rec_safety x0 uu = match x0, uu with Unused, uu -> Unused
                           | PastRec, Unused -> Unused
                           | NonFutuRec, Unused -> Unused
                           | AnyRec, Unused -> Unused
                           | AnyRec, PastRec -> AnyRec
                           | AnyRec, NonFutuRec -> AnyRec
                           | AnyRec, AnyRec -> AnyRec
                           | PastRec, AnyRec -> AnyRec
                           | NonFutuRec, AnyRec -> AnyRec
                           | PastRec, PastRec -> PastRec
                           | PastRec, NonFutuRec -> PastRec
                           | NonFutuRec, PastRec -> PastRec
                           | NonFutuRec, NonFutuRec -> NonFutuRec;;

let rec sup_rec_safety x0 uu = match x0, uu with AnyRec, uu -> AnyRec
                         | Unused, AnyRec -> AnyRec
                         | PastRec, AnyRec -> AnyRec
                         | NonFutuRec, AnyRec -> AnyRec
                         | NonFutuRec, Unused -> NonFutuRec
                         | NonFutuRec, PastRec -> NonFutuRec
                         | NonFutuRec, NonFutuRec -> NonFutuRec
                         | Unused, NonFutuRec -> NonFutuRec
                         | PastRec, NonFutuRec -> NonFutuRec
                         | PastRec, Unused -> PastRec
                         | PastRec, PastRec -> PastRec
                         | Unused, PastRec -> PastRec
                         | Unused, Unused -> Unused;;

let rec safe_letpast
  p x1 = match p, x1 with p, Eq (t1, t2) -> Unused
    | p, Less (t1, t2) -> Unused
    | p, LessEq (t1, t2) -> Unused
    | p, Pred (e, ts) ->
        (if equal_proda equal_string8 equal_nat p (e, size_lista ts)
          then NonFutuRec else Unused)
    | p, Let (e, phi, psi) ->
        sup_rec_safety
          (times_rec_safety (safe_letpast (e, nfv phi) psi)
            (safe_letpast p phi))
          (if equal_proda equal_string8 equal_nat p (e, nfv phi) then Unused
            else safe_letpast p psi)
    | p, LetPast (e, phi, psi) ->
        (if equal_proda equal_string8 equal_nat p (e, nfv phi) then Unused
          else sup_rec_safety
                 (times_rec_safety (safe_letpast (e, nfv phi) psi)
                   (safe_letpast p phi))
                 (safe_letpast p psi))
    | p, Neg phi -> safe_letpast p phi
    | p, Or (phi, psi) ->
        sup_rec_safety (safe_letpast p phi) (safe_letpast p psi)
    | p, And (phi, psi) ->
        sup_rec_safety (safe_letpast p phi) (safe_letpast p psi)
    | p, Ands l -> fold (comp sup_rec_safety (safe_letpast p)) l Unused
    | p, Exists (ty, phi) -> safe_letpast p phi
    | p, Agg (y, omega, b, f, phi) -> safe_letpast p phi
    | p, Prev (i, phi) -> times_rec_safety PastRec (safe_letpast p phi)
    | p, Next (i, phi) -> times_rec_safety AnyRec (safe_letpast p phi)
    | p, Since (phi, i, psi) ->
        sup_rec_safety (safe_letpast p phi)
          (times_rec_safety (if memL i zero_nata then NonFutuRec else PastRec)
            (safe_letpast p psi))
    | p, Until (phi, i, psi) ->
        times_rec_safety AnyRec
          (sup_rec_safety (safe_letpast p phi) (safe_letpast p psi))
    | p, MatchP (i, r) ->
        fold sup_rec_safety
          (csorted_list_of_set (ceq_rec_safety, ccompare_rec_safety)
            (atms (ceq_rec_safety, ccompare_rec_safety, set_impl_rec_safety)
              (map_regex (safe_letpast p) r)))
          Unused
    | p, MatchF (i, r) ->
        times_rec_safety AnyRec
          (fold sup_rec_safety
            (csorted_list_of_set (ceq_rec_safety, ccompare_rec_safety)
              (atms (ceq_rec_safety, ccompare_rec_safety, set_impl_rec_safety)
                (map_regex (safe_letpast p) r)))
            Unused)
    | p, TP t -> Unused
    | p, TS t -> Unused;;

let rec is_Var = function Var x1 -> true
                 | Const x2 -> false
                 | Plus (x31, x32) -> false
                 | Minus (x41, x42) -> false
                 | UMinus x5 -> false
                 | Mult (x61, x62) -> false
                 | Div (x71, x72) -> false
                 | Mod (x81, x82) -> false
                 | F2i x9 -> false
                 | I2f x10 -> false;;

let rec remove_neg = function Neg phi -> phi
                     | Pred (v, va) -> Pred (v, va)
                     | Let (v, va, vb) -> Let (v, va, vb)
                     | Frz (v, va, vb) -> Frz (v, va, vb)
                     | LetPast (v, va, vb) -> LetPast (v, va, vb)
                     | Eq (v, va) -> Eq (v, va)
                     | Less (v, va) -> Less (v, va)
                     | LessEq (v, va) -> LessEq (v, va)
                     | Or (v, va) -> Or (v, va)
                     | And (v, va) -> And (v, va)
                     | Ands v -> Ands v
                     | Exists (v, va) -> Exists (v, va)
                     | Agg (v, va, vb, vc, vd) -> Agg (v, va, vb, vc, vd)
                     | Prev (v, va) -> Prev (v, va)
                     | Next (v, va) -> Next (v, va)
                     | Since (v, va, vb) -> Since (v, va, vb)
                     | Until (v, va, vb) -> Until (v, va, vb)
                     | Trigger (v, va, vb) -> Trigger (v, va, vb)
                     | Release (v, va, vb) -> Release (v, va, vb)
                     | MatchF (v, va) -> MatchF (v, va)
                     | MatchP (v, va) -> MatchP (v, va)
                     | TP v -> TP v
                     | TS v -> TS v;;

let rec safe_formula
  = function
    Eq (t1, t2) ->
      is_Const t1 && (is_Const t2 || is_Var t2) || is_Var t1 && is_Const t2
    | Less (t1, t2) -> false
    | LessEq (t1, t2) -> false
    | Pred (e, ts) -> list_all (fun t -> is_Var t || is_Const t) ts
    | Let (p, phi, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
          (atLeastLessThan
            (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
            zero_nata (nfv phi))
          (fvi zero_nata phi) &&
          (safe_formula phi && safe_formula psi)
    | Frz (p, phi, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
          (atLeastLessThan
            (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
            zero_nata (nfv phi))
          (fvi zero_nata phi) &&
          (safe_formula phi && safe_formula psi)
    | LetPast (p, phi, psi) ->
        less_eq_rec_safety (safe_letpast (p, nfv phi) phi) PastRec &&
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
             (atLeastLessThan
               (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
               zero_nata (nfv phi))
             (fvi zero_nata phi) &&
            (safe_formula phi && safe_formula psi))
    | Neg phi ->
        is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
          (fvi zero_nata phi) &&
          safe_formula phi
    | Or (phi, psi) ->
        set_eq (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata psi)
          (fvi zero_nata phi) &&
          (safe_formula phi && safe_formula psi)
    | And (phi, psi) ->
        safe_formula phi &&
          (safe_assignment (fvi zero_nata phi) psi ||
            (safe_formula psi ||
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata psi)
                (fvi zero_nata phi) &&
                (is_constraint psi ||
                  (match psi with Pred (_, _) -> false | Let (_, _, _) -> false
                    | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                    | Eq (_, _) -> false | Less (_, _) -> false
                    | LessEq (_, _) -> false | Neg a -> safe_formula a
                    | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                    | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                    | Prev (_, _) -> false | Next (_, _) -> false
                    | Since (_, _, _) -> false | Until (_, _, _) -> false
                    | Trigger (a, b, c) -> safe_dual true safe_formula a b c
                    | Release (phia, i, psia) ->
                      bounded i &&
                        (not (memL i zero_nata && memR i zero_nata) &&
                          (safe_formula phia &&
                            (safe_formula psia &&
                              (set_eq (cenum_nat, ceq_nat, ccompare_nat)
                                 (fvi zero_nata phia) (fvi zero_nata psia) &&
                                safe_formula
                                  (and_release_safe_bounded phi phia i psia)))))
                    | MatchF (_, _) -> false | MatchP (_, _) -> false
                    | TP _ -> false | TS _ -> false))))
    | Ands l ->
        (let (pos, neg) = partition safe_formula l in
          not (null pos) &&
            (list_all safe_formula (mapa remove_neg neg) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (mapa (fvi zero_nata) neg)))
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (mapa (fvi zero_nata) pos)))))
    | Exists (t, phi) ->
        safe_formula phi &&
          member (ceq_nat, ccompare_nat) zero_nata (fvi zero_nata phi)
    | Agg (y, omega, tys, f, phi) ->
        safe_formula phi &&
          (not (member (ceq_nat, ccompare_nat) (plus_nata y (size_lista tys))
                 (fvi zero_nata phi)) &&
            (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
               (atLeastLessThan
                 (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
                 zero_nata (size_lista tys))
               (fvi zero_nata phi) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                (fvi_trm zero_nata f) (fvi zero_nata phi)))
    | Prev (i, phi) -> safe_formula phi
    | Next (i, phi) -> safe_formula phi
    | Since (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          ((safe_formula phi ||
             (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
               | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
               | Eq (_, _) -> false | Less (_, _) -> false
               | LessEq (_, _) -> false | Neg a -> safe_formula a
               | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
               | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
               | Prev (_, _) -> false | Next (_, _) -> false
               | Since (_, _, _) -> false | Until (_, _, _) -> false
               | Trigger (_, _, _) -> false | Release (_, _, _) -> false
               | MatchF (_, _) -> false | MatchP (_, _) -> false | TP _ -> false
               | TS _ -> false)) &&
            safe_formula psi)
    | Until (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          ((safe_formula phi ||
             (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
               | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
               | Eq (_, _) -> false | Less (_, _) -> false
               | LessEq (_, _) -> false | Neg a -> safe_formula a
               | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
               | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
               | Prev (_, _) -> false | Next (_, _) -> false
               | Since (_, _, _) -> false | Until (_, _, _) -> false
               | Trigger (_, _, _) -> false | Release (_, _, _) -> false
               | MatchF (_, _) -> false | MatchP (_, _) -> false | TP _ -> false
               | TS _ -> false)) &&
            safe_formula psi)
    | Trigger (phi, i, psi) -> safe_dual false safe_formula phi i psi
    | Release (phi, i, psi) ->
        memL i zero_nata && memR i zero_nata &&
          (bounded i &&
            (safe_formula psi &&
              (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                 (fvi zero_nata phi) (fvi zero_nata psi) &&
                safe_formula (release_safe_0 phi i psi))))
    | MatchP (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            safe_formula phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                  | Eq (_, _) -> false | Less (_, _) -> false
                  | LessEq (_, _) -> false | Neg a -> safe_formula a
                  | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | Trigger (_, _, _) -> false | Release (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Past Strict r
    | MatchF (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            safe_formula phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                  | Eq (_, _) -> false | Less (_, _) -> false
                  | LessEq (_, _) -> false | Neg a -> safe_formula a
                  | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | Trigger (_, _, _) -> false | Release (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Futu Strict r
    | TP t -> is_Var t || is_Const t
    | TS t -> is_Var t || is_Const t;;

let rec to_mregex_exec
  x0 xs = match x0, xs with Skip n, xs -> (MSkip n, xs)
    | Test phi, xs ->
        (if safe_formula phi then (MTestPos (size_lista xs), xs @ [phi])
          else (match phi with Pred (_, _) -> (MSkip zero_nata, xs)
                 | Let (_, _, _) -> (MSkip zero_nata, xs)
                 | Frz (_, _, _) -> (MSkip zero_nata, xs)
                 | LetPast (_, _, _) -> (MSkip zero_nata, xs)
                 | Eq (_, _) -> (MSkip zero_nata, xs)
                 | Less (_, _) -> (MSkip zero_nata, xs)
                 | LessEq (_, _) -> (MSkip zero_nata, xs)
                 | Neg phia -> (MTestNeg (size_lista xs), xs @ [phia])
                 | Or (_, _) -> (MSkip zero_nata, xs)
                 | And (_, _) -> (MSkip zero_nata, xs)
                 | Ands _ -> (MSkip zero_nata, xs)
                 | Exists (_, _) -> (MSkip zero_nata, xs)
                 | Agg (_, _, _, _, _) -> (MSkip zero_nata, xs)
                 | Prev (_, _) -> (MSkip zero_nata, xs)
                 | Next (_, _) -> (MSkip zero_nata, xs)
                 | Since (_, _, _) -> (MSkip zero_nata, xs)
                 | Until (_, _, _) -> (MSkip zero_nata, xs)
                 | Trigger (_, _, _) -> (MSkip zero_nata, xs)
                 | Release (_, _, _) -> (MSkip zero_nata, xs)
                 | MatchF (_, _) -> (MSkip zero_nata, xs)
                 | MatchP (_, _) -> (MSkip zero_nata, xs)
                 | TP _ -> (MSkip zero_nata, xs)
                 | TS _ -> (MSkip zero_nata, xs)))
    | Plusa (r, s), xs ->
        (let (mr, ys) = to_mregex_exec r xs in
         let (ms, a) = to_mregex_exec s ys in
          (MPlus (mr, ms), a))
    | Times (r, s), xs ->
        (let (mr, ys) = to_mregex_exec r xs in
         let (ms, a) = to_mregex_exec s ys in
          (MTimes (mr, ms), a))
    | Star r, xs -> (let (mr, a) = to_mregex_exec r xs in (MStar mr, a));;

let rec to_mregex r = to_mregex_exec r [];;

let rec check_wty_regex
  check_wty_formula x1 = match check_wty_formula, x1 with
    check_wty_formula, Skip l -> true
    | check_wty_formula, Test phi -> check_wty_formula phi
    | check_wty_formula, Plusa (r, s) ->
        check_wty_regex check_wty_formula r &&
          check_wty_regex check_wty_formula s
    | check_wty_formula, Times (r, s) ->
        check_wty_regex check_wty_formula r &&
          check_wty_regex check_wty_formula s
    | check_wty_formula, Star r -> check_wty_regex check_wty_formula r;;

let rec check_wty_formula
  = function Let (p, phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | Frz (p, phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | Neg phi -> check_wty_formula phi
    | Or (phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | And (phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | Ands phi_s -> foldl (fun a x -> a && check_wty_formula x) true phi_s
    | Exists (t, phi) -> check_wty_formula phi
    | Agg (y, (agg_type, d), tys, trm, phi) ->
        (match d with TAny _ -> false | TNum _ -> false
          | TCst _ -> check_wty_formula phi)
    | Prev (i, phi) -> check_wty_formula phi
    | Next (i, phi) -> check_wty_formula phi
    | Since (phi, i, psi) -> check_wty_formula phi && check_wty_formula psi
    | Until (phi, i, psi) -> check_wty_formula phi && check_wty_formula psi
    | Trigger (phi, i, psi) -> check_wty_formula phi && check_wty_formula psi
    | Release (phi, i, psi) -> check_wty_formula phi && check_wty_formula psi
    | MatchF (i, r) -> check_wty_regex check_wty_formula r
    | MatchP (i, r) -> check_wty_regex check_wty_formula r
    | LetPast (p, phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | Pred (v, va) -> true
    | Eq (v, va) -> true
    | Less (v, va) -> true
    | LessEq (v, va) -> true
    | TP v -> true
    | TS v -> true;;

let rec convert_tysym = function TCst a -> a
                        | TAny v -> TFloat
                        | TNum v -> TFloat;;

let rec type_check
  s phi =
    bindb (check s (fun a -> TAny a) phi)
      (fun f ->
        (if check_wty_formula (map_formula f phi)
          then Inr (map_formula (comp convert_tysym f) phi)
          else Inl "failed to infer ground type for aggregation result"));;

let rec de_ginit_evt
  args =
    (empty_queue,
      (empty_queue,
        (empty_queue, (zero_nata, (true, (edl_mempty_nat, (edl_bot, [])))))));;

let dq_empty : 'a dq = Dq ([], [], zero_nata, zero_nata);;

let rec de_ginit_dq
  args =
    (zero_nata,
      (empty_queue,
        (empty_queue,
          (zero_nata,
            (join_mask (args_n args) (args_L args),
              (join_mask (args_n args) (args_R args),
                (edl_bot,
                  (edl_mempty_nat,
                    (dq_push edl_mempty_tstp dq_empty, (dq_empty, []))))))))));;

let rec evt_applies
  args =
    is_none (args_agg args) &&
      (is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) (args_L args) &&
        memL (args_ivl args) zero_nata);;

let rec gainit_dq args ag = (de_ginit_dq args, dinit_maggauxa ag);;

let rec init_u_d
  ago args msk =
    (match ago
      with None ->
        (if evt_applies args then (fun () -> (MUD_evt (de_ginit_evt args)))
          else (fun () -> (MUD_dns (de_ginit_dq args))))
      | Some ag -> (fun () -> (MUD_agg (ag, gainit_dq args ag))));;

let rec deopt x = mapa the x;;

let rec reopt x = mapa (fun a -> Some a) x;;

let rec part _B
  f pivot x2 = match f, pivot, x2 with f, pivot, [] -> ([], ([], []))
    | f, pivot, x :: xs ->
        (let (lts, (eqs, gts)) = part _B f pivot xs in
         let xa = f x in
          (if less _B.order_linorder.preorder_order.ord_preorder xa pivot
            then (x :: lts, (eqs, gts))
            else (if less _B.order_linorder.preorder_order.ord_preorder pivot xa
                   then (lts, (eqs, x :: gts)) else (lts, (x :: eqs, gts)))));;

let rec sort_key _B
  f xs =
    (match xs with [] -> [] | [_] -> xs
      | [x; y] ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then xs else [y; x])
      | _ :: _ :: _ :: _ ->
        (let (lts, (eqs, gts)) =
           part _B f
             (f (nth xs
                  (divide_nata (size_lista xs) (nat_of_integer (Z.of_int 2)))))
             xs
           in
          sort_key _B f lts @ eqs @ sort_key _B f gts));;

let rec sorted_list_of_set (_A1, _A2, _A3, _A4)
  = function
    RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "sorted_list_of_set RBT_set: ccompare = None"
            (fun _ -> sorted_list_of_set (_A1, _A2, _A3, _A4) (RBT_set rbt))
        | Some _ -> sort_key _A4 (fun x -> x) (keysb _A2 rbt))
    | DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "sorted_list_of_set DList_set: ceq = None"
              (fun _ -> sorted_list_of_set (_A1, _A2, _A3, _A4) (DList_set dxs))
          | Some _ -> sort_key _A4 (fun x -> x) (list_of_dlist _A1 dxs))
    | Set_Monad xs -> sort_key _A4 (fun x -> x) (remdups _A3 xs);;

let ed_mempty_rank : (((event_data option) list), list_aux) mapping
  = RBT_Mapping (emptyc (ccompare_list (ccompare_option ccompare_event_data)));;

let ed_mempty_sum : (((event_data option) list), (nat * Z.t)) mapping
  = RBT_Mapping (emptyc (ccompare_list (ccompare_option ccompare_event_data)));;

let ed_mempty_nat : (((event_data option) list), nat) mapping
  = RBT_Mapping (emptyc (ccompare_list (ccompare_option ccompare_event_data)));;

let rec init_maggaux
  args =
    (let aggtype = fst (aggargs_omega args) in
     let y0 = snd (aggargs_omega args) in
      (match (aggtype, y0) with (Agg_Cnt, _) -> (true, CntAux ed_mempty_nat)
        | (Agg_Min, TInt) -> (true, RankAux (ed_mempty_rank, IntT))
        | (Agg_Min, TFloat) -> (false, CntAux ed_mempty_nat)
        | (Agg_Min, TString) -> (true, RankAux (ed_mempty_rank, StringT))
        | (Agg_Max, TInt) -> (true, RankAux (ed_mempty_rank, IntT))
        | (Agg_Max, TFloat) -> (false, CntAux ed_mempty_nat)
        | (Agg_Max, TString) -> (true, RankAux (ed_mempty_rank, StringT))
        | (Agg_Sum, TInt) -> (true, SumAux ed_mempty_sum)
        | (Agg_Sum, TFloat) -> (false, CntAux ed_mempty_nat)
        | (Agg_Sum, TString) -> (false, CntAux ed_mempty_nat)
        | (Agg_Avg, TInt) -> (true, SumAux ed_mempty_sum)
        | (Agg_Avg, TFloat) -> (false, CntAux ed_mempty_nat)
        | (Agg_Avg, TString) -> (false, CntAux ed_mempty_nat)
        | (Agg_Med, TInt) -> (false, CntAux ed_mempty_nat)
        | (Agg_Med, TFloat) -> (true, RankAux (ed_mempty_rank, IntT))
        | (Agg_Med, TString) -> (false, CntAux ed_mempty_nat)));;

let rec init_maggauxa
  args =
    (match init_maggaux args with (true, aux) -> Some aux
      | (false, _) -> None);;

let ed_mempty_tstp : (((event_data option) list), (nat, nat) sum) mapping
  = RBT_Mapping (emptyc (ccompare_list (ccompare_option ccompare_event_data)));;

let rec init_mmuaux
  args =
    (zero_nata,
      (empty_queue,
        (empty_queue,
          (zero_nata,
            (join_mask (args_n args) (args_L args),
              (join_mask (args_n args) (args_R args),
                (ed_bot,
                  (ed_mempty_nat,
                    (updateb (ccompare_nat, equal_nat) zero_nata ed_mempty_tstp
                       (mapping_empty ccompare_nat
                         (of_phantom mapping_impl_nata)),
                      (mapping_empty ccompare_nat
                         (of_phantom mapping_impl_nata),
                        []))))))))));;

let rec init_mmauaux
  args =
    (init_mmuaux args,
      (match args_agg args with None -> None | Some a -> init_maggauxa a));;

let rec init_dq
  args =
    (zero_nata,
      (empty_queue,
        (empty_queue,
          (zero_nata,
            (join_mask (args_n args) (args_L args),
              (join_mask (args_n args) (args_R args),
                (ed_bot,
                  (ed_mempty_nat,
                    (dq_push ed_mempty_tstp dq_empty, (dq_empty, []))))))))));;

let rec init_muaux_dq
  args =
    (if is_none (args_agg args) then MU_dq (init_dq args)
      else MU_agg (init_mmauaux args));;

let rec idx_create (_A1, _A2)
  t x = cluster
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
            set_impl_list)
          (ccompare_list (ccompare_option _A2))
          (comp (fun a -> Some a) (restrict x)) t;;

let rec wf_idx_of_set (_A1, _A2)
  xc xd xe xf =
    Abs_wf_idx
      (let a = xd in
       let i = inf_seta (ceq_nat, ccompare_nat) xe a in
        (xc, (a, (i, idx_create (_A1, _A2)
                       (filter
                         ((ceq_list (ceq_option _A1)),
                           (ccompare_list (ccompare_option _A2)))
                         (wf_tuple xc a) xf)
                       i))));;

let rec wf_table_of_set_args (_A1, _A2)
  args x =
    (if is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) (args_L args) ||
          set_eq (cenum_nat, ceq_nat, ccompare_nat) (args_L args) (args_R args)
      then Wf_table_of_set (args_n args, args_R args, x)
      else Wf_table_of_idx
             (wf_idx_of_set (_A1, _A2) (args_n args) (args_R args) (args_L args)
               x));;

let rec ed_init_mmsaux
  args =
    (zero_nata,
      (zero_nata,
        (join_mask (args_n args) (args_L args),
          (join_mask (args_n args) (args_R args),
            (empty_queue,
              (empty_queue,
                (ed_bot,
                  (wf_table_of_set_args (ceq_event_data, ccompare_event_data)
                     args ed_bot,
                    (ed_mempty_nat,
                      (wf_table_of_set_args
                         (ceq_event_data, ccompare_event_data) args ed_bot,
                        ed_mempty_nat))))))))));;

let rec init_mmasaux
  args =
    (match args_agg args with None -> (ed_init_mmsaux args, None)
      | Some aggargs -> (ed_init_mmsaux args, init_maggauxa aggargs));;

let rec ed_init_mmtaux
  args =
    (zero_nata,
      (zero_nata,
        (zero_nata,
          (zero_nata,
            (join_mask (args_n args) (args_L args),
              (join_mask (args_n args) (args_R args),
                (empty_queue,
                  (empty_queue,
                    (ed_mempty_nat,
                      (ed_bot, (ed_mempty_nat, (ed_bot, ed_bot))))))))))));;

let rec split_constraint
  = function Eq (t1, t2) -> (t1, (true, (MEq, t2)))
    | Less (t1, t2) -> (t1, (true, (MLess, t2)))
    | LessEq (t1, t2) -> (t1, (true, (MLessEq, t2)))
    | Neg (Eq (t1, t2)) -> (t1, (false, (MEq, t2)))
    | Neg (Less (t1, t2)) -> (t1, (false, (MLess, t2)))
    | Neg (LessEq (t1, t2)) -> (t1, (false, (MLessEq, t2)))
    | Pred (v, va) -> failwith "undefined"
    | Let (v, va, vb) -> failwith "undefined"
    | Frz (v, va, vb) -> failwith "undefined"
    | LetPast (v, va, vb) -> failwith "undefined"
    | Neg (Pred (va, vb)) -> failwith "undefined"
    | Neg (Let (va, vb, vc)) -> failwith "undefined"
    | Neg (Frz (va, vb, vc)) -> failwith "undefined"
    | Neg (LetPast (va, vb, vc)) -> failwith "undefined"
    | Neg (Neg va) -> failwith "undefined"
    | Neg (Or (va, vb)) -> failwith "undefined"
    | Neg (And (va, vb)) -> failwith "undefined"
    | Neg (Ands va) -> failwith "undefined"
    | Neg (Exists (va, vb)) -> failwith "undefined"
    | Neg (Agg (va, vb, vc, vd, ve)) -> failwith "undefined"
    | Neg (Prev (va, vb)) -> failwith "undefined"
    | Neg (Next (va, vb)) -> failwith "undefined"
    | Neg (Since (va, vb, vc)) -> failwith "undefined"
    | Neg (Until (va, vb, vc)) -> failwith "undefined"
    | Neg (Trigger (va, vb, vc)) -> failwith "undefined"
    | Neg (Release (va, vb, vc)) -> failwith "undefined"
    | Neg (MatchF (va, vb)) -> failwith "undefined"
    | Neg (MatchP (va, vb)) -> failwith "undefined"
    | Neg (TP va) -> failwith "undefined"
    | Neg (TS va) -> failwith "undefined"
    | Or (v, va) -> failwith "undefined"
    | And (v, va) -> failwith "undefined"
    | Ands v -> failwith "undefined"
    | Exists (v, va) -> failwith "undefined"
    | Agg (v, va, vb, vc, vd) -> failwith "undefined"
    | Prev (v, va) -> failwith "undefined"
    | Next (v, va) -> failwith "undefined"
    | Since (v, va, vb) -> failwith "undefined"
    | Until (v, va, vb) -> failwith "undefined"
    | Trigger (v, va, vb) -> failwith "undefined"
    | Release (v, va, vb) -> failwith "undefined"
    | MatchF (v, va) -> failwith "undefined"
    | MatchP (v, va) -> failwith "undefined"
    | TP v -> failwith "undefined"
    | TS v -> failwith "undefined";;

let rec split_assignment
  x xa1 = match x, xa1 with
    x, Eq (t1, t2) ->
      (match (t1, t2)
        with (Var xa, Var y) ->
          (if member (ceq_nat, ccompare_nat) xa x then (y, t1) else (xa, t2))
        | (Var xa, Const _) -> (xa, t2) | (Var xa, Plus (_, _)) -> (xa, t2)
        | (Var xa, Minus (_, _)) -> (xa, t2) | (Var xa, UMinus _) -> (xa, t2)
        | (Var xa, Mult (_, _)) -> (xa, t2) | (Var xa, Div (_, _)) -> (xa, t2)
        | (Var xa, Mod (_, _)) -> (xa, t2) | (Var xa, F2i _) -> (xa, t2)
        | (Var xa, I2f _) -> (xa, t2) | (Const _, Var y) -> (y, t1)
        | (Plus (_, _), Var y) -> (y, t1) | (Minus (_, _), Var y) -> (y, t1)
        | (UMinus _, Var y) -> (y, t1) | (Mult (_, _), Var y) -> (y, t1)
        | (Div (_, _), Var y) -> (y, t1) | (Mod (_, _), Var y) -> (y, t1)
        | (F2i _, Var y) -> (y, t1) | (I2f _, Var y) -> (y, t1))
    | uu, Pred (v, va) -> failwith "undefined"
    | uu, Let (v, va, vb) -> failwith "undefined"
    | uu, Frz (v, va, vb) -> failwith "undefined"
    | uu, LetPast (v, va, vb) -> failwith "undefined"
    | uu, Less (v, va) -> failwith "undefined"
    | uu, LessEq (v, va) -> failwith "undefined"
    | uu, Neg v -> failwith "undefined"
    | uu, Or (v, va) -> failwith "undefined"
    | uu, And (v, va) -> failwith "undefined"
    | uu, Ands v -> failwith "undefined"
    | uu, Exists (v, va) -> failwith "undefined"
    | uu, Agg (v, va, vb, vc, vd) -> failwith "undefined"
    | uu, Prev (v, va) -> failwith "undefined"
    | uu, Next (v, va) -> failwith "undefined"
    | uu, Since (v, va, vb) -> failwith "undefined"
    | uu, Until (v, va, vb) -> failwith "undefined"
    | uu, Trigger (v, va, vb) -> failwith "undefined"
    | uu, Release (v, va, vb) -> failwith "undefined"
    | uu, MatchF (v, va) -> failwith "undefined"
    | uu, MatchP (v, va) -> failwith "undefined"
    | uu, TP v -> failwith "undefined"
    | uu, TS v -> failwith "undefined";;

let rec is_simple_pattern
  x0 uu = match x0, uu with [], uu -> true
    | Var y :: ts, x -> less_eq_nat x y && is_simple_pattern ts (suc y)
    | Const vb :: va, uw -> false
    | Plus (vb, vc) :: va, uw -> false
    | Minus (vb, vc) :: va, uw -> false
    | UMinus vb :: va, uw -> false
    | Mult (vb, vc) :: va, uw -> false
    | Div (vb, vc) :: va, uw -> false
    | Mod (vb, vc) :: va, uw -> false
    | F2i vb :: va, uw -> false
    | I2f vb :: va, uw -> false;;

let rec is_copy_pattern
  n ts = equal_lista equal_trm ts (mapa (fun a -> Var a) (upt zero_nata n));;

let rec pred_mode_of
  n ts =
    (if is_copy_pattern n ts then Copy
      else (if is_simple_pattern ts zero_nata then Simple else Match));;

let rec init_aggargs
  cols n g0 y omega tys f = Aggargs_ext (cols, n, g0, y, omega, tys, f, ());;

let rec mtrm_of_trm = function Var x -> MVar x
                      | Const x -> MConst x
                      | Plus (v, va) -> failwith "undefined"
                      | Minus (v, va) -> failwith "undefined"
                      | UMinus v -> failwith "undefined"
                      | Mult (v, va) -> failwith "undefined"
                      | Div (v, va) -> failwith "undefined"
                      | Mod (v, va) -> failwith "undefined"
                      | F2i v -> failwith "undefined"
                      | I2f v -> failwith "undefined";;

let rec meinit0
  n x1 = match n, x1 with
    n, Neg phi ->
      (if is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
            (fvi zero_nata phi)
        then MNeg (meinit0 n phi) else MRel ed_bot)
    | n, Eq (t1, t2) -> MRel (eq_rel n t1 t2)
    | n, Pred (e, ts) -> MPred (e, ts, pred_mode_of n ts)
    | n, Let (p, phi, psi) ->
        MLet (p, nfv phi, meinit0 (nfv phi) phi, meinit0 n psi)
    | n, Frz (p, phi, psi) ->
        MFrz (p, nfv phi, meinit0 (nfv phi) phi, meinit0 n psi, zero_nata,
               zero_nata, zero_nata, [])
    | n, LetPast (p, phi, psi) ->
        MLetPast
          (p, nfv phi, meinit0 (nfv phi) phi, meinit0 n psi, zero_nata, None)
    | n, Or (phi, psi) ->
        MOr (meinit0 n phi, meinit0 n psi, (mbuf_t_empty, mbuf_t_empty))
    | n, And (phi, psi) ->
        (if safe_assignment (fvi zero_nata phi) psi
          then MAndAssign
                 (meinit0 n phi, split_assignment (fvi zero_nata phi) psi)
          else (if safe_formula psi
                 then MAnd (fvi zero_nata phi, meinit0 n phi, true,
                             fvi zero_nata psi, meinit0 n psi,
                             (mbuf_t_empty, mbuf_t_empty))
                 else (if is_constraint psi
                        then MAndRel (meinit0 n phi, split_constraint psi)
                        else (match psi with Pred (_, _) -> MRel ed_bot
                               | Let (_, _, _) -> MRel ed_bot
                               | Frz (_, _, _) -> MRel ed_bot
                               | LetPast (_, _, _) -> MRel ed_bot
                               | Eq (_, _) -> MRel ed_bot
                               | Less (_, _) -> MRel ed_bot
                               | LessEq (_, _) -> MRel ed_bot
                               | Neg psia ->
                                 MAnd (fvi zero_nata phi, meinit0 n phi, false,
fvi zero_nata psia, meinit0 n psia, (mbuf_t_empty, mbuf_t_empty))
                               | Or (_, _) -> MRel ed_bot
                               | And (_, _) -> MRel ed_bot
                               | Ands _ -> MRel ed_bot
                               | Exists (_, _) -> MRel ed_bot
                               | Agg (_, _, _, _, _) -> MRel ed_bot
                               | Prev (_, _) -> MRel ed_bot
                               | Next (_, _) -> MRel ed_bot
                               | Since (_, _, _) -> MRel ed_bot
                               | Until (_, _, _) -> MRel ed_bot
                               | Trigger (phia, i, psia) ->
                                 (let args =
                                    (fun b ->
                                      init_args i n (fvi zero_nata phia)
(fvi zero_nata psia) b None)
                                    in
                                   (if safe_formula phia
                                     then MAndTrigger
    (fvi zero_nata phi, meinit0 n phi, (mbuf_t_empty, mbuf_t_empty), args true,
      meinit0 n phia, meinit0 n psia, (mbuf_t_empty, mbuf_t_empty),
      mbuf_t_empty, ed_init_mmtaux (args true))
                                     else (match phia
    with Pred (_, _) -> MRel ed_bot | Let (_, _, _) -> MRel ed_bot
    | Frz (_, _, _) -> MRel ed_bot | LetPast (_, _, _) -> MRel ed_bot
    | Eq (_, _) -> MRel ed_bot | Less (_, _) -> MRel ed_bot
    | LessEq (_, _) -> MRel ed_bot
    | Neg phiaa ->
      MAndTrigger
        (fvi zero_nata phi, meinit0 n phi, (mbuf_t_empty, mbuf_t_empty),
          args false, meinit0 n phiaa, meinit0 n psia,
          (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
          ed_init_mmtaux (args false))
    | Or (_, _) -> MRel ed_bot | And (_, _) -> MRel ed_bot
    | Ands _ -> MRel ed_bot | Exists (_, _) -> MRel ed_bot
    | Agg (_, _, _, _, _) -> MRel ed_bot | Prev (_, _) -> MRel ed_bot
    | Next (_, _) -> MRel ed_bot | Since (_, _, _) -> MRel ed_bot
    | Until (_, _, _) -> MRel ed_bot | Trigger (_, _, _) -> MRel ed_bot
    | Release (_, _, _) -> MRel ed_bot | MatchF (_, _) -> MRel ed_bot
    | MatchP (_, _) -> MRel ed_bot | TP _ -> MRel ed_bot
    | TS _ -> MRel ed_bot)))
                               | Release (phia, i, psia) ->
                                 meinit0 n
                                   (and_release_safe_bounded phi phia i psia)
                               | MatchF (_, _) -> MRel ed_bot
                               | MatchP (_, _) -> MRel ed_bot
                               | TP _ -> MRel ed_bot | TS _ -> MRel ed_bot))))
    | n, Ands l ->
        (let (pos, neg) = partition safe_formula l in
         let mpos = mapa (meinit0 n) pos in
         let mneg = mapa (meinit0 n) (mapa remove_neg neg) in
         let vpos = mapa (fvi zero_nata) pos in
         let vneg = mapa (fvi zero_nata) neg in
          MAnds (vpos, vneg, mpos @ mneg,
                  replicate (size_lista l) mbuf_t_empty))
    | n, Exists (t, phi) -> MExists (meinit0 (suc n) phi)
    | n, Agg (y, omega, tys, f, phi) ->
        (let default =
           MAgg (init_aggargs (fvi zero_nata phi) n
                   (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                     (fvi zero_nata phi)
                     (atLeastLessThan
                       (ceq_nat, ccompare_nat, equal_nat, interval_nat,
                         set_impl_nat)
                       zero_nata (size_lista tys)))
                   y omega tys f,
                  meinit0 (plus_nata (size_lista tys) n) phi)
           in
          (match phi with Pred (_, _) -> default | Let (_, _, _) -> default
            | Frz (_, _, _) -> default | LetPast (_, _, _) -> default
            | Eq (_, _) -> default | Less (_, _) -> default
            | LessEq (_, _) -> default | Neg _ -> default | Or (_, _) -> default
            | And (_, _) -> default | Ands _ -> default
            | Exists (_, _) -> default | Agg (_, _, _, _, _) -> default
            | Prev (_, _) -> default | Next (_, _) -> default
            | Since (phia, i, psi) ->
              (let agg =
                 Some (init_aggargs (fvi zero_nata phi) n
                        (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                          (fvi zero_nata phi)
                          (atLeastLessThan
                            (ceq_nat, ccompare_nat, equal_nat, interval_nat,
                              set_impl_nat)
                            zero_nata (size_lista tys)))
                        y omega tys f)
                 in
               let args =
                 (fun b ->
                   init_args i (plus_nata (size_lista tys) n)
                     (fvi zero_nata phia) (fvi zero_nata psi) b agg)
                 in
                (if safe_formula phia
                  then MSince
                         (args true,
                           meinit0 (plus_nata (size_lista tys) n) phia,
                           meinit0 (plus_nata (size_lista tys) n) psi,
                           (mbuf_t_empty,
                             (mbuf_t_empty, (mbuf_t_empty, false))),
                           init_mmasaux (args true))
                  else (match phia with Pred (_, _) -> MRel ed_bot
                         | Let (_, _, _) -> MRel ed_bot
                         | Frz (_, _, _) -> MRel ed_bot
                         | LetPast (_, _, _) -> MRel ed_bot
                         | Eq (_, _) -> MRel ed_bot | Less (_, _) -> MRel ed_bot
                         | LessEq (_, _) -> MRel ed_bot
                         | Neg phib ->
                           MSince
                             (args false,
                               meinit0 (plus_nata (size_lista tys) n) phib,
                               meinit0 (plus_nata (size_lista tys) n) psi,
                               (mbuf_t_empty,
                                 (mbuf_t_empty, (mbuf_t_empty, false))),
                               init_mmasaux (args false))
                         | Or (_, _) -> MRel ed_bot | And (_, _) -> MRel ed_bot
                         | Ands _ -> MRel ed_bot | Exists (_, _) -> MRel ed_bot
                         | Agg (_, _, _, _, _) -> MRel ed_bot
                         | Prev (_, _) -> MRel ed_bot
                         | Next (_, _) -> MRel ed_bot
                         | Since (_, _, _) -> MRel ed_bot
                         | Until (_, _, _) -> MRel ed_bot
                         | Trigger (_, _, _) -> MRel ed_bot
                         | Release (_, _, _) -> MRel ed_bot
                         | MatchF (_, _) -> MRel ed_bot
                         | MatchP (_, _) -> MRel ed_bot | TP _ -> MRel ed_bot
                         | TS _ -> MRel ed_bot)))
            | Until (phia, i, psi) ->
              (let agg =
                 Some (init_aggargs (fvi zero_nata phi) n
                        (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                          (fvi zero_nata phi)
                          (atLeastLessThan
                            (ceq_nat, ccompare_nat, equal_nat, interval_nat,
                              set_impl_nat)
                            zero_nata (size_lista tys)))
                        y omega tys f)
                 in
               let args =
                 (fun b ->
                   init_args i (plus_nata (size_lista tys) n)
                     (fvi zero_nata phia) (fvi zero_nata psi) b agg)
                 in
                (if safe_formula phia
                  then MUntil
                         (args true,
                           meinit0 (plus_nata (size_lista tys) n) phia,
                           meinit0 (plus_nata (size_lista tys) n) psi,
                           (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                           zero_nata, init_muaux_dq (args true))
                  else (match phia with Pred (_, _) -> MRel ed_bot
                         | Let (_, _, _) -> MRel ed_bot
                         | Frz (_, _, _) -> MRel ed_bot
                         | LetPast (_, _, _) -> MRel ed_bot
                         | Eq (_, _) -> MRel ed_bot | Less (_, _) -> MRel ed_bot
                         | LessEq (_, _) -> MRel ed_bot
                         | Neg phib ->
                           MUntil
                             (args false,
                               meinit0 (plus_nata (size_lista tys) n) phib,
                               meinit0 (plus_nata (size_lista tys) n) psi,
                               (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                               zero_nata, init_muaux_dq (args false))
                         | Or (_, _) -> MRel ed_bot | And (_, _) -> MRel ed_bot
                         | Ands _ -> MRel ed_bot | Exists (_, _) -> MRel ed_bot
                         | Agg (_, _, _, _, _) -> MRel ed_bot
                         | Prev (_, _) -> MRel ed_bot
                         | Next (_, _) -> MRel ed_bot
                         | Since (_, _, _) -> MRel ed_bot
                         | Until (_, _, _) -> MRel ed_bot
                         | Trigger (_, _, _) -> MRel ed_bot
                         | Release (_, _, _) -> MRel ed_bot
                         | MatchF (_, _) -> MRel ed_bot
                         | MatchP (_, _) -> MRel ed_bot | TP _ -> MRel ed_bot
                         | TS _ -> MRel ed_bot)))
            | Trigger (_, _, _) -> default | Release (_, _, _) -> default
            | MatchF (_, _) -> default | MatchP (_, _) -> default
            | TP _ -> default | TS _ -> default))
    | n, Prev (i, phi) ->
        MPrev (i, meinit0 n phi, true, mbuf_t_empty, mbuf_t_empty)
    | n, Next (i, phi) -> MNext (i, meinit0 n phi, true, mbuf_t_empty)
    | n, Since (phi, i, psi) ->
        (let args =
           (fun b ->
             init_args i n (fvi zero_nata phi) (fvi zero_nata psi) b None)
           in
          (if safe_formula phi
            then MSince
                   (args true, meinit0 n phi, meinit0 n psi,
                     (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))),
                     init_mmasaux (args true))
            else (match phi with Pred (_, _) -> MRel ed_bot
                   | Let (_, _, _) -> MRel ed_bot | Frz (_, _, _) -> MRel ed_bot
                   | LetPast (_, _, _) -> MRel ed_bot | Eq (_, _) -> MRel ed_bot
                   | Less (_, _) -> MRel ed_bot | LessEq (_, _) -> MRel ed_bot
                   | Neg phia ->
                     MSince
                       (args false, meinit0 n phia, meinit0 n psi,
                         (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))),
                         init_mmasaux (args false))
                   | Or (_, _) -> MRel ed_bot | And (_, _) -> MRel ed_bot
                   | Ands _ -> MRel ed_bot | Exists (_, _) -> MRel ed_bot
                   | Agg (_, _, _, _, _) -> MRel ed_bot
                   | Prev (_, _) -> MRel ed_bot | Next (_, _) -> MRel ed_bot
                   | Since (_, _, _) -> MRel ed_bot
                   | Until (_, _, _) -> MRel ed_bot
                   | Trigger (_, _, _) -> MRel ed_bot
                   | Release (_, _, _) -> MRel ed_bot
                   | MatchF (_, _) -> MRel ed_bot | MatchP (_, _) -> MRel ed_bot
                   | TP _ -> MRel ed_bot | TS _ -> MRel ed_bot)))
    | n, Until (phi, i, psi) ->
        (let args =
           (fun b ->
             init_args i n (fvi zero_nata phi) (fvi zero_nata psi) b None)
           in
          (if safe_formula phi
            then MUntil
                   (args true, meinit0 n phi, meinit0 n psi,
                     (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty, zero_nata,
                     init_muaux_dq (args true))
            else (match phi with Pred (_, _) -> MRel ed_bot
                   | Let (_, _, _) -> MRel ed_bot | Frz (_, _, _) -> MRel ed_bot
                   | LetPast (_, _, _) -> MRel ed_bot | Eq (_, _) -> MRel ed_bot
                   | Less (_, _) -> MRel ed_bot | LessEq (_, _) -> MRel ed_bot
                   | Neg phia ->
                     MUntil
                       (args false, meinit0 n phia, meinit0 n psi,
                         (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty, zero_nata,
                         init_muaux_dq (args false))
                   | Or (_, _) -> MRel ed_bot | And (_, _) -> MRel ed_bot
                   | Ands _ -> MRel ed_bot | Exists (_, _) -> MRel ed_bot
                   | Agg (_, _, _, _, _) -> MRel ed_bot
                   | Prev (_, _) -> MRel ed_bot | Next (_, _) -> MRel ed_bot
                   | Since (_, _, _) -> MRel ed_bot
                   | Until (_, _, _) -> MRel ed_bot
                   | Trigger (_, _, _) -> MRel ed_bot
                   | Release (_, _, _) -> MRel ed_bot
                   | MatchF (_, _) -> MRel ed_bot | MatchP (_, _) -> MRel ed_bot
                   | TP _ -> MRel ed_bot | TS _ -> MRel ed_bot)))
    | n, Trigger (phi, i, psi) ->
        (let args =
           (fun b ->
             init_args i n (fvi zero_nata phi) (fvi zero_nata psi) b None)
           in
          (if safe_formula phi
            then MTrigger
                   (args true, meinit0 n phi, meinit0 n psi,
                     (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                     ed_init_mmtaux (args true))
            else (match phi with Pred (_, _) -> MRel ed_bot
                   | Let (_, _, _) -> MRel ed_bot | Frz (_, _, _) -> MRel ed_bot
                   | LetPast (_, _, _) -> MRel ed_bot | Eq (_, _) -> MRel ed_bot
                   | Less (_, _) -> MRel ed_bot | LessEq (_, _) -> MRel ed_bot
                   | Neg phia ->
                     MTrigger
                       (args false, meinit0 n phia, meinit0 n psi,
                         (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                         ed_init_mmtaux (args false))
                   | Or (_, _) -> MRel ed_bot | And (_, _) -> MRel ed_bot
                   | Ands _ -> MRel ed_bot | Exists (_, _) -> MRel ed_bot
                   | Agg (_, _, _, _, _) -> MRel ed_bot
                   | Prev (_, _) -> MRel ed_bot | Next (_, _) -> MRel ed_bot
                   | Since (_, _, _) -> MRel ed_bot
                   | Until (_, _, _) -> MRel ed_bot
                   | Trigger (_, _, _) -> MRel ed_bot
                   | Release (_, _, _) -> MRel ed_bot
                   | MatchF (_, _) -> MRel ed_bot | MatchP (_, _) -> MRel ed_bot
                   | TP _ -> MRel ed_bot | TS _ -> MRel ed_bot)))
    | n, Release (phi, i, psi) ->
        (if memL i zero_nata && memR i zero_nata
          then meinit0 n (release_safe_0 phi i psi)
          else meinit0 n (release_safe_bounded phi i psi))
    | n, MatchP (i, r) ->
        (let (mr, phi_s) = to_mregex r in
          MMatchP
            (i, mr,
              sorted_list_of_set
                (ceq_mregex, ccompare_mregex, equal_mregex, linorder_mregex)
                (rPDs mr),
              mapa (meinit0 n) phi_s, replicate (size_lista phi_s) mbuf_t_empty,
              mbuf_t_empty, []))
    | n, MatchF (i, r) ->
        (let (mr, phi_s) = to_mregex r in
          MMatchF
            (i, mr,
              sorted_list_of_set
                (ceq_mregex, ccompare_mregex, equal_mregex, linorder_mregex)
                (lPDs mr),
              mapa (meinit0 n) phi_s, replicate (size_lista phi_s) mbuf_t_empty,
              mbuf_t_empty, zero_nata, []))
    | n, TP ta -> MTP (mtrm_of_trm ta, zero_nata)
    | n, TS ta -> MTS (mtrm_of_trm ta)
    | n, Less (v, va) -> MRel ed_bot
    | n, LessEq (v, va) -> MRel ed_bot;;

let rec minit0 n phi = Rep_meformula (meinit0 n phi);;

let rec minit
  phi = (let n = nfv phi in
          Mestate (zero_nata, zero_nata, minit0 n phi, n, empty_queue, ()));;

let rec get_and_list = function Ands l -> (if null l then [Ands l] else l)
                       | Pred (v, va) -> [Pred (v, va)]
                       | Let (v, va, vb) -> [Let (v, va, vb)]
                       | Frz (v, va, vb) -> [Frz (v, va, vb)]
                       | LetPast (v, va, vb) -> [LetPast (v, va, vb)]
                       | Eq (v, va) -> [Eq (v, va)]
                       | Less (v, va) -> [Less (v, va)]
                       | LessEq (v, va) -> [LessEq (v, va)]
                       | Neg v -> [Neg v]
                       | Or (v, va) -> [Or (v, va)]
                       | And (v, va) -> [And (v, va)]
                       | Exists (v, va) -> [Exists (v, va)]
                       | Agg (v, va, vb, vc, vd) -> [Agg (v, va, vb, vc, vd)]
                       | Prev (v, va) -> [Prev (v, va)]
                       | Next (v, va) -> [Next (v, va)]
                       | Since (v, va, vb) -> [Since (v, va, vb)]
                       | Until (v, va, vb) -> [Until (v, va, vb)]
                       | Trigger (v, va, vb) -> [Trigger (v, va, vb)]
                       | Release (v, va, vb) -> [Release (v, va, vb)]
                       | MatchF (v, va) -> [MatchF (v, va)]
                       | MatchP (v, va) -> [MatchP (v, va)]
                       | TP v -> [TP v]
                       | TS v -> [TS v];;

let rec aggargs_n
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_n;;

let rec dagg_fused
  n cs args =
    (match args_agg args with None -> false
      | Some ag ->
        equal_lista equal_nat cs (dagg_cols ag) &&
          (equal_lista equal_nat (set_cols (args_R args))
             (dagg_child_cols ag) &&
            (superset equal_nat (dagg_child_cols ag) (set_cols (args_L args)) &&
              (equal_nata n (aggargs_n ag) &&
                equal_nata (args_n args)
                  (plus_nata (size_lista (aggargs_tys ag)) (aggargs_n ag))))));;

let rec is_simple_eq
  t1 t2 =
    is_Const t1 && (is_Const t2 || is_Var t2) || is_Var t1 && is_Const t2;;

let rec dnode_n
  n args =
    (match args_agg args with None -> n
      | Some ag -> plus_nata (size_lista (aggargs_tys ag)) (aggargs_n ag));;

let rec dagg_gcolsa
  (g0, (omega, (f, (k, pos)))) w =
    upt zero_nata pos @ upt (suc pos) (suc (minus_nata w k));;

let rec dagg_ccols
  (g0, (omega, (f, (k, pos)))) w =
    upt zero_nata k @
      mapa (fun c -> plus_nata c k)
        (dagg_gcolsa (g0, (omega, (f, (k, pos)))) w);;

let rec shift_trm
  b x1 = match b, x1 with b, Var x -> Var (if less_nat x b then x else suc x)
    | b, Const c -> Const c
    | b, Plus (a, c) -> Plus (shift_trm b a, shift_trm b c)
    | b, Minus (a, c) -> Minus (shift_trm b a, shift_trm b c)
    | b, UMinus a -> UMinus (shift_trm b a)
    | b, Mult (a, c) -> Mult (shift_trm b a, shift_trm b c)
    | b, Div (a, c) -> Div (shift_trm b a, shift_trm b c)
    | b, Mod (a, c) -> Mod (shift_trm b a, shift_trm b c)
    | b, F2i a -> F2i (shift_trm b a)
    | b, I2f a -> I2f (shift_trm b a);;

let rec dagg_args
  (g0, (omega, (f, (k, pos)))) w =
    Aggargs_ext
      (set (ceq_nat, ccompare_nat, set_impl_nat)
         (dagg_ccols (g0, (omega, (f, (k, pos)))) w),
        suc (minus_nata w k), g0, pos, omega, replicate k TInt,
        shift_trm (plus_nata k pos) f, ());;

let rec ag_init p w = init_maggauxa (dagg_args p w);;

let rec sum_list _A
  xs = foldr (plus _A.semigroup_add_monoid_add.plus_semigroup_add) xs
         (zero _A.zero_monoid_add);;

let rec dfail_nodes
  = function DFail -> one_nata
    | DAnds (ps, ns, l, buf) -> sum_list monoid_add_nat (mapa dfail_nodes l)
    | DAnd (pl, phi, pos, psi, buf) ->
        plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DAndRel (phi, conf) -> dfail_nodes phi
    | DOr (phi, psi, buf) -> plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DNeg phi -> dfail_nodes phi
    | DExists (phi, b) -> dfail_nodes phi
    | DAgg (g0, omega, f, k, pos, phi) -> dfail_nodes phi
    | DPrev (i, phi, f, buf, nts) -> dfail_nodes phi
    | DNext (i, phi, f, nts) -> dfail_nodes phi
    | DSince (args, phi, psi, buf, aux) ->
        plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DUntil (args, msk, phi, psi, buf, nts, t, aux) ->
        plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DAndAssign (p, t, phi) -> dfail_nodes phi
    | DLet (p, m, phi, psi) -> plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DFrz (p, m, phi, psi, jfrz, jpsi0, jphi, alpha_s) ->
        plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DLetPast (p, m, phi, psi, i, buf) ->
        plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DTrigger (dags, phi, psi, dbuf, nts, daux) ->
        plus_nata (dfail_nodes phi) (dfail_nodes psi)
    | DAndTrigger (pl, phia, buf1, dags, phi, psi, buf2, nts, daux) ->
        plus_nata (plus_nata (dfail_nodes phia) (dfail_nodes phi))
          (dfail_nodes psi)
    | DMatchP (i, mr, mrs, msks, phi_s, buf, nts, aux) ->
        sum_list monoid_add_nat (mapa dfail_nodes phi_s)
    | DMatchF (i, mr, mrs, msks, phi_s, buf, nts, t, aux) ->
        sum_list monoid_add_nat (mapa dfail_nodes phi_s)
    | DRel v -> zero_nata
    | DPredS (v, va) -> zero_nata
    | DPredM (v, va, vb, vc) -> zero_nata
    | DTP (v, va) -> zero_nata
    | DTS v -> zero_nata;;

let rec equal_pred_mode x0 x1 = match x0, x1 with Simple, Match -> false
                          | Match, Simple -> false
                          | Copy, Match -> false
                          | Match, Copy -> false
                          | Copy, Simple -> false
                          | Simple, Copy -> false
                          | Match, Match -> true
                          | Simple, Simple -> true
                          | Copy, Copy -> true;;

let rec de_ginit_mmtaux
  args msk =
    (zero_nata,
      (zero_nata,
        (zero_nata,
          (zero_nata,
            (msk, (empty_queue,
                    (empty_queue,
                      (edl_mempty_nat,
                        (edl_bot,
                          (edl_mempty_nat, (edl_bot, edl_bot)))))))))));;

let rec edl_image_of_wide
  h (RBT_set rbt) =
    foldb (ccompare_list (ccompare_option ccompare_event_data))
      (fun x -> edl_insert (h x)) rbt edl_bot;;

let rec de_deopt_table x = edl_image_of_wide deopt x;;

let rec deopt_table (_A1, _A2)
  x = image ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        ((ceq_list _A1), (ccompare_list _A2), set_impl_list) deopt x;;

let rec reindex_constraint
  cs conf =
    (let (t1, (p, (c, t2))) = conf in
      (reindex_trm cs t1, (p, (c, reindex_trm cs t2))));;

let rec dformula_of
  hp n cs x3 = match hp, n, cs, x3 with
    hp, n, cs, MAnds (a_pos, a_neg, l, buf) ->
      (match a_pos with [] -> (fun () -> DFail)
        | a :: asa ->
          (let cs_pos = set_cols a :: mapa set_cols asa in
           let fin = dands_cols (set_cols a) (mapa set_cols asa) in
           let cs_neg = mapa set_cols a_neg in
            (if not (equal_nata (size_lista l)
                      (plus_nata (size_lista a_pos) (size_lista a_neg)))
              then (fun () -> DFail)
              else binda (hmap (fun (aa, b) -> dformula_of hp n aa b)
                           (zip (cs_pos @ cs_neg) l))
                     (fun ld ->
                       (fun () ->
                         (DAnds
                           (dands_plans (set_cols a) (mapa set_cols asa),
                             mapa (mk_djoin fin) cs_neg, ld,
                             mapa (fun _ -> mbuf_t_empty) ld)))))))
    | hp, n, cs, MPred (e, tms, mode) ->
        (fun () ->
          (if not (equal_pred_mode mode Match) &&
                equal_lista equal_nat cs (tms_cols tms)
            then DPredS (e, size_lista tms)
            else DPredM (e, size_lista tms, tms, cs)))
    | hp, n, cs, MRel rel ->
        (fun () ->
          (DRel (de_deopt_table
                  (dnarrow
                    ((ceq_option ceq_event_data),
                      (ccompare_option ccompare_event_data))
                    (wide_mask n cs) rel))))
    | hp, n, cs, MAnd (a, phi, pos, b, psi, buf) ->
        binda (dformula_of hp n (set_cols a) phi)
          (fun phi_d ->
            binda (dformula_of hp n (set_cols b) psi)
              (fun psi_d ->
                (fun () ->
                  (DAnd (mk_djoin (set_cols a) (set_cols b), phi_d, pos, psi_d,
                          (mbuf_t_empty, mbuf_t_empty))))))
    | hp, n, cs, MAndRel (phi, conf) ->
        binda (dformula_of hp n cs phi)
          (fun phi_d ->
            (fun () -> (DAndRel (phi_d, reindex_constraint cs conf))))
    | hp, n, cs, MOr (phi, psi, buf) ->
        binda (dformula_of hp n cs phi)
          (fun phi_d ->
            binda (dformula_of hp n cs psi)
              (fun psi_d ->
                (fun () -> (DOr (phi_d, psi_d, (mbuf_t_empty, mbuf_t_empty))))))
    | hp, n, cs, MNeg phi ->
        binda (dformula_of hp n [] phi) (fun phi_d -> (fun () -> (DNeg phi_d)))
    | hp, n, cs, MExists phi ->
        (match mcols (suc n) phi with None -> (fun () -> DFail)
          | Some ccs ->
            binda (dformula_of hp (suc n) ccs phi)
              (fun phi_d ->
                (fun () ->
                  (DExists
                    (phi_d,
                      (match ccs with [] -> false
                        | c :: _ -> equal_nata c zero_nata))))))
    | hp, n, cs, MAgg (args, phi) ->
        binda (dformula_of hp (plus_nata (size_lista (aggargs_tys args)) n)
                (dagg_child_cols args) phi)
          (fun phi_d ->
            (fun () ->
              (DAgg (aggargs_g0 args, aggargs_omega args,
                      reindex_trm (dagg_child_cols args) (aggargs_f args),
                      size_lista (aggargs_tys args), dagg_pos args, phi_d))))
    | hp, n, cs, MPrev (i, phi, first, buf, nts) ->
        binda (dformula_of hp n cs phi)
          (fun phi_d ->
            (fun () -> (DPrev (i, phi_d, first, mbuf_t_empty, nts))))
    | hp, n, cs, MNext (i, phi, first, nts) ->
        binda (dformula_of hp n cs phi)
          (fun phi_d -> (fun () -> (DNext (i, phi_d, first, nts))))
    | hp, n, cs, MSince (args, phi, psi, buf, aux) ->
        (let cs_L = set_cols (args_L args) in
          (if sevt_applies args
            then binda (dformula_of hp n cs_L phi)
                   (fun phi_d ->
                     binda (dformula_of hp n (set_cols (args_R args)) psi)
                       (fun psi_d ->
                         binda (init_d hp None args
                                 (dmsk (set_cols (args_R args)) cs_L))
                           (fun q ->
                             (fun () ->
                               (DSince
                                 (args, phi_d, psi_d,
                                   (mbuf_t_empty,
                                     (mbuf_t_empty, (mbuf_t_empty, false))),
                                   q))))))
            else (if is_none (args_agg args) &&
                       (equal_nata (args_n args) n &&
                         (set_eq (cenum_nat, ceq_nat, ccompare_nat)
                            (args_R args)
                            (set (ceq_nat, ccompare_nat, set_impl_nat) cs) &&
                           superset equal_nat cs cs_L))
                   then (let dags = dargs cs cs_L args in
                          binda (dformula_of hp n cs_L phi)
                            (fun phi_d ->
                              binda (dformula_of hp n cs psi)
                                (fun psi_d ->
                                  binda (init_d hp None dags (dmsk cs cs_L))
                                    (fun q ->
                                      (fun () ->
(DSince
  (dags, phi_d, psi_d, (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))),
    q)))))))
                   else (if dagg_fused n cs args
                          then (let ag = the (args_agg args) in
                                let ccs = dagg_child_cols ag in
                                let dags = dargs ccs cs_L (dunfuse args) in
                                 binda (dformula_of hp (args_n args) cs_L phi)
                                   (fun phi_d ->
                                     binda (dformula_of hp (args_n args) ccs
     psi)
                                       (fun psi_d ->
 binda (init_d hp (Some (dagg_of ag)) dags (dmsk ccs cs_L))
   (fun q ->
     (fun () ->
       (DSince
         (dags, phi_d, psi_d,
           (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))), q)))))))
                          else (fun () -> DFail)))))
    | hp, n, cs, MUntil (args, phi, psi, buf, nts, t, aux) ->
        (let cs_L = set_cols (args_L args) in
          (if evt_applies args
            then binda (dformula_of hp n cs_L phi)
                   (fun phi_d ->
                     binda (dformula_of hp n (set_cols (args_R args)) psi)
                       (fun psi_d ->
                         binda (init_u_d None args
                                 (dmsk (set_cols (args_R args)) cs_L))
                           (fun d ->
                             (fun () ->
                               (DUntil
                                 (args, dmsk (set_cols (args_R args)) cs_L,
                                   phi_d, psi_d, (mbuf_t_empty, mbuf_t_empty),
                                   nts, t, d))))))
            else (if is_none (args_agg args) &&
                       (equal_nata (args_n args) n &&
                         (set_eq (cenum_nat, ceq_nat, ccompare_nat)
                            (args_R args)
                            (set (ceq_nat, ccompare_nat, set_impl_nat) cs) &&
                           superset equal_nat cs cs_L))
                   then (let dags = dargs cs cs_L args in
                          binda (dformula_of hp n cs_L phi)
                            (fun phi_d ->
                              binda (dformula_of hp n cs psi)
                                (fun psi_d ->
                                  binda (init_u_d None dags (dmsk cs cs_L))
                                    (fun d ->
                                      (fun () ->
(DUntil
  (dags, dmsk cs cs_L, phi_d, psi_d, (mbuf_t_empty, mbuf_t_empty), nts, t,
    d)))))))
                   else (if dagg_fused n cs args
                          then (let ag = the (args_agg args) in
                                let ccs = dagg_child_cols ag in
                                let dags = dargs ccs cs_L (dunfuse args) in
                                 binda (dformula_of hp (args_n args) cs_L phi)
                                   (fun phi_d ->
                                     binda (dformula_of hp (args_n args) ccs
     psi)
                                       (fun psi_d ->
 binda (init_u_d (Some (dagg_of ag)) dags (dmsk ccs cs_L))
   (fun d ->
     (fun () ->
       (DUntil
         (dags, dmsk ccs cs_L, phi_d, psi_d, (mbuf_t_empty, mbuf_t_empty), nts,
           t, d)))))))
                          else (fun () -> DFail)))))
    | hp, n, cs, MAndAssign (phi, conf) ->
        (let y = fst conf in
         let t = snd conf in
         let cs0 = rem_col cs y in
          (if membera equal_nat cs y &&
                less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                  (fvi_trm zero_nata t)
                  (set (ceq_nat, ccompare_nat, set_impl_nat) cs0)
            then binda (dformula_of hp n cs0 phi)
                   (fun phi_d ->
                     (fun () ->
                       (DAndAssign (ins_pos cs0 y, reindex_trm cs0 t, phi_d))))
            else (fun () -> DFail)))
    | hp, n, cs, MLet (p, m, phi, psi) ->
        binda (dformula_of false m (upt zero_nata m) phi)
          (fun phi_d ->
            binda (dformula_of false n cs psi)
              (fun psi_d -> (fun () -> (DLet (p, m, phi_d, psi_d)))))
    | hp, n, cs, MTP (mt, i) ->
        (fun () ->
          (if equal_lista equal_nat cs (mtrm_dcols mt) then DTP (mt, i)
            else DFail))
    | hp, n, cs, MTS mt ->
        (fun () ->
          (if equal_lista equal_nat cs (mtrm_dcols mt) then DTS mt else DFail))
    | hp, n, cs, MMatchP (i, mr, mrs, phi_s, buf, nts, aux) ->
        (match those (mapa (mcols n) phi_s) with None -> (fun () -> DFail)
          | Some css ->
            (if equal_lista equal_nat cs (fold merge_cols css [])
              then binda (hmap (fun (a, b) -> dformula_of false n a b)
                           (zip css phi_s))
                     (fun ld ->
                       (fun () ->
                         (DMatchP
                           (i, mr, mrs, mapa (dmsk cs) css, ld,
                             mapa (fun _ -> mbuf_t_empty) ld, mbuf_t_empty,
                             []))))
              else (fun () -> DFail)))
    | hp, n, cs, MMatchF (i, mr, mrs, phi_s, buf, nts, t, aux) ->
        (match those (mapa (mcols n) phi_s) with None -> (fun () -> DFail)
          | Some css ->
            (if equal_lista equal_nat cs (fold merge_cols css [])
              then binda (hmap (fun (a, b) -> dformula_of false n a b)
                           (zip css phi_s))
                     (fun ld ->
                       (fun () ->
                         (DMatchF
                           (i, mr, mrs, mapa (dmsk cs) css, ld,
                             mapa (fun _ -> mbuf_t_empty) ld, mbuf_t_empty, t,
                             []))))
              else (fun () -> DFail)))
    | hp, n, cs, MTrigger (args, phi, psi, buf, nts, aux) ->
        (let cs_L = set_cols (args_L args) in
          (if equal_nata (args_n args) n &&
                (set_eq (cenum_nat, ceq_nat, ccompare_nat) (args_R args)
                   (set (ceq_nat, ccompare_nat, set_impl_nat) cs) &&
                  (superset equal_nat cs cs_L &&
                    (memL (args_ivl args) zero_nata &&
                      memR (args_ivl args) zero_nata)))
            then (let dags = dargs cs cs_L args in
                   binda (dformula_of hp n cs_L phi)
                     (fun phi_d ->
                       binda (dformula_of hp n cs psi)
                         (fun psi_d ->
                           (fun () ->
                             (DTrigger
                               (dags, phi_d, psi_d,
                                 (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                                 de_ginit_mmtaux dags (dmsk cs cs_L)))))))
            else (fun () -> DFail)))
    | hp, n, cs, MAndTrigger (v, phia, buf1, args, phi, psi, buf2, nts, aux) ->
        (let cs_V = set_cols v in
         let cs_R = set_cols (args_R args) in
         let cs_L = set_cols (args_L args) in
          (if equal_nata (args_n args) n &&
                (equal_lista equal_nat cs (merge_cols cs_V cs_R) &&
                  (superset equal_nat cs_V cs_R &&
                    superset equal_nat cs_R cs_L))
            then (let dags = dargs cs_R cs_L args in
                   binda (dformula_of hp n cs_V phia)
                     (fun phi_d ->
                       binda (dformula_of hp n cs_L phi)
                         (fun phi_da ->
                           binda (dformula_of hp n cs_R psi)
                             (fun psi_d ->
                               (fun () ->
                                 (DAndTrigger
                                   (mk_djoin cs_V cs_R, phi_d,
                                     (mbuf_t_empty, mbuf_t_empty), dags, phi_da,
                                     psi_d, (mbuf_t_empty, mbuf_t_empty),
                                     mbuf_t_empty,
                                     de_ginit_mmtaux dags
                                       (dmsk cs_R cs_L))))))))
            else (fun () -> DFail)))
    | hp, n, cs, MLetPast (p, m, phi, psi, i, buf) ->
        binda (dformula_of false m (upt zero_nata m) phi)
          (fun phi_d ->
            binda (dformula_of false n cs psi)
              (fun psi_d ->
                (fun () ->
                  (DLetPast
                    (p, m, phi_d, psi_d, i,
                      map_option
                        (comp (deopt_table
                                (ceq_event_data, ccompare_event_data))
                          (dnarrow
                            ((ceq_option ceq_event_data),
                              (ccompare_option ccompare_event_data))
                            (wide_mask m (upt zero_nata m))))
                        buf)))))
    | hp, n, cs, MFrz (p, m, phi, psi, jfrz, jpsi0, jphi, alpha_s) ->
        binda (dformula_of false m (upt zero_nata m) phi)
          (fun phi_d ->
            binda (dformula_of false n cs psi)
              (fun psi_d ->
                (fun () ->
                  (DFrz (p, m, phi_d, psi_d, jfrz, jpsi0, jphi,
                          mapa (comp (deopt_table
                                       (ceq_event_data, ccompare_event_data))
                                 (dnarrow
                                   ((ceq_option ceq_event_data),
                                     (ccompare_option ccompare_event_data))
                                   (wide_mask m (upt zero_nata m))))
                            alpha_s)))));;

let rec de_gsw_init
  args = (zero_nata, (empty_queue, (empty_queue, (edl_mempty_nat, edl_bot))));;

let rec usa_init args p = (de_gsw_init args, ag_init p (args_n args));;

let rec udsx_init_agg args p = UDSX_wagg (p, usa_init args p);;

let rec uuw_init
  args =
    (empty_queue,
      (empty_queue,
        (empty_queue, (zero_nata, (true, ((edl_mempty_nat, edl_bot), []))))));;

let rec udux_init
  args =
    (if is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) (args_L args) &&
          memL (args_ivl args) zero_nata
      then UDUX_win (uuw_init args) else UDUX_gen (de_ginit_dq args));;

let rec udsx_init
  args msk =
    (if is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) (args_L args)
      then UDSX_win (de_gsw_init args)
      else UDSX_gen (de_ginit_msaux args msk));;

let rec dagg_gcols
  args =
    mapa (fun c -> minus_nata c (size_lista (aggargs_tys args)))
      (drop (size_lista (aggargs_tys args)) (set_cols (aggargs_cols args)));;

let rec udof
  n cs x2 = match n, cs, x2 with
    n, cs, MRel rel ->
      UDRel (de_deopt_table
              (dtabc
                ((ceq_option ceq_event_data),
                  (ccompare_option ccompare_event_data))
                n cs rel))
    | n, cs, MPred (e, tms, mode) ->
        (if equal_pred_mode mode Match then UDPredM (e, size_lista tms, tms, cs)
          else (if equal_pred_mode mode Copy &&
                     (equal_lista equal_trm tms
                        (mapa (fun a -> Var a) (upt zero_nata n)) &&
                       equal_lista equal_nat cs (upt zero_nata n)) ||
                     equal_pred_mode mode Simple &&
                       (is_simple_pattern tms zero_nata &&
                         equal_lista equal_nat cs (smp_cols tms))
                 then UDPredS (e, size_lista tms) else UDFail))
    | n, cs, MAndRel (phi, conf) ->
        (if less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
              (fvi_trm zero_nata (fst conf))
              (set (ceq_nat, ccompare_nat, set_impl_nat) cs) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                (fvi_trm zero_nata (snd (snd (snd conf))))
                (set (ceq_nat, ccompare_nat, set_impl_nat) cs)
          then UDAndRel (udof n cs phi, reindex_constraint cs conf) else UDFail)
    | n, cs, MNeg phi -> (if null cs then UDNeg (udof n [] phi) else UDFail)
    | n, cs, MExists phi ->
        UDExists (udof (suc n) (zero_nata :: mapa suc cs) phi, true)
    | n, cs, MOr (phi, psi, buf) ->
        (if mbuf_t_is_empty (fst buf) && mbuf_t_is_empty (snd buf)
          then UDOr (udof n cs phi, udof n cs psi, (mbuf_t_empty, mbuf_t_empty))
          else UDFail)
    | n, cs, MAnd (a, phi, pos, b, psi, buf) ->
        (let cs1 = set_cols a in
         let cs2 = set_cols b in
          (if equal_lista equal_nat cs (merge_cols cs1 cs2) &&
                ((pos || less_eq_set (cenum_nat, ceq_nat, ccompare_nat) b a) &&
                  (mbuf_t_is_empty (fst buf) && mbuf_t_is_empty (snd buf)))
            then UDAnd (mk_djoin cs1 cs2, udof n cs1 phi, pos, udof n cs2 psi,
                         (mbuf_t_empty, mbuf_t_empty))
            else UDFail))
    | n, cs, MPrev (i, phi, first, buf, nts) ->
        (if mbuf_t_is_empty buf
          then UDPrev (i, udof n cs phi, first, mbuf_t_empty, nts) else UDFail)
    | n, cs, MNext (i, phi, first, nts) -> UDNext (i, udof n cs phi, first, nts)
    | n, cs, MAnds (a_pos, a_neg, l, buf) ->
        (match a_pos with [] -> UDFail
          | a :: asa ->
            (let c0 = set_cols a in
             let css = mapa set_cols asa in
             let nss = mapa set_cols a_neg in
              (if equal_lista equal_nat cs (dands_cols c0 css) &&
                    (equal_nata (size_lista l)
                       (plus_nata (size_lista a_pos) (size_lista a_neg)) &&
                      list_all mbuf_t_is_empty buf)
                then UDAnds
                       (dands_plans c0 css, dands_plans (dands_cols c0 css) nss,
                         mapa (fun (aa, b) -> udof n aa b)
                           (zip (c0 :: css @ nss) l),
                         mapa (fun _ -> mbuf_t_empty) l)
                else UDFail)))
    | n, cs, MAgg (args, phi) ->
        (let m = size_lista (aggargs_tys args) in
         let g = dagg_gcols args in
         let y = aggargs_y args in
          (if equal_lista equal_nat cs (merge_cols g [y]) &&
                equal_lista equal_nat (set_cols (aggargs_cols args))
                  (upt zero_nata m @ mapa (fun c -> plus_nata c m) g)
            then UDAgg (aggargs_g0 args, aggargs_omega args,
                         reindex_trm
                           (upt zero_nata m @ mapa (fun c -> plus_nata c m) g)
                           (aggargs_f args),
                         m, ins_pos g y,
                         udof (plus_nata m n)
                           (upt zero_nata m @ mapa (fun c -> plus_nata c m) g)
                           phi)
            else UDFail))
    | n, cs, MSince (args, phi, psi, buf, aux) ->
        (let cs_L = set_cols (args_L args) in
         let cs_R = set_cols (args_R args) in
         let phi_d = udof (dnode_n n args) cs_L phi in
         let psi_d = udof (dnode_n n args) cs_R psi in
         let bf =
           (let (a, (b, (c, d))) = buf in
             (rep_mbuf_t a, (rep_mbuf_t b, (rep_mbuf_t c, d))))
           in
          (match args_agg args
            with None ->
              (if equal_nata (args_n args) n &&
                    (equal_lista equal_nat cs cs_R &&
                      (superset equal_nat cs_R cs_L &&
                        equal_proda
                          (equal_list
                            (equal_set
                              (cenum_list,
                                (ceq_list (ceq_option ceq_event_data)),
                                (ccompare_list
                                  (ccompare_option ccompare_event_data)),
                                (equal_list (equal_option equal_event_data)))))
                          (equal_prod
                            (equal_list
                              (equal_set
                                (cenum_list,
                                  (ceq_list (ceq_option ceq_event_data)),
                                  (ccompare_list
                                    (ccompare_option ccompare_event_data)),
                                  (equal_list
                                    (equal_option equal_event_data)))))
                            (equal_prod (equal_list equal_nat) equal_bool))
                          bf ([], ([], ([], false)))))
                then UDSince
                       (dargs cs cs_L args, phi_d, psi_d,
                         (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))),
                         udsx_init (dargs cs cs_L args) (dmsk cs cs_L))
                else UDFail)
            | Some ag ->
              (let m = size_lista (aggargs_tys ag) in
               let g = dagg_gcols ag in
               let y = aggargs_y ag in
                (if equal_nata (args_n args) (plus_nata m (aggargs_n ag)) &&
                      (equal_nata (aggargs_n ag) n &&
                        (superset equal_nat cs_R cs_L &&
                          (equal_proda
                             (equal_list
                               (equal_set
                                 (cenum_list,
                                   (ceq_list (ceq_option ceq_event_data)),
                                   (ccompare_list
                                     (ccompare_option ccompare_event_data)),
                                   (equal_list
                                     (equal_option equal_event_data)))))
                             (equal_prod
                               (equal_list
                                 (equal_set
                                   (cenum_list,
                                     (ceq_list (ceq_option ceq_event_data)),
                                     (ccompare_list
                                       (ccompare_option ccompare_event_data)),
                                     (equal_list
                                       (equal_option equal_event_data)))))
                               (equal_prod (equal_list equal_nat) equal_bool))
                             bf ([], ([], ([], false))) &&
                            (equal_lista equal_nat
                               (upt zero_nata m @
                                 mapa (fun c -> plus_nata c m) g)
                               cs_R &&
                              (equal_lista equal_nat cs (merge_cols g [y]) &&
                                (sorted_wrt less_nat g &&
                                   list_all (fun c -> less_nat c n) g &&
                                  (less_nat y n &&
                                    (not (membera equal_nat g y) &&
                                      ((if aggargs_g0 ag then null g
 else true) &&
less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
  (fvi_trm zero_nata (aggargs_f ag))
  (set (ceq_nat, ccompare_nat, set_impl_nat) cs_R))))))))))
                  then (if is_empty
                             (card_UNIV_nat, ceq_nat, cproper_interval_nat)
                             (cpos cs_R
                               (set (ceq_nat, ccompare_nat, set_impl_nat) cs_L))
                         then UDSince
                                (dargs cs_R cs_L args, phi_d, psi_d,
                                  (mbuf_t_empty,
                                    (mbuf_t_empty, (mbuf_t_empty, false))),
                                  udsx_init_agg (dargs cs_R cs_L args)
                                    (aggargs_g0 ag,
                                      (aggargs_omega ag,
(reindex_trm cs_R (aggargs_f ag), (m, ins_pos g y)))))
                         else UDAgg (aggargs_g0 ag, aggargs_omega ag,
                                      reindex_trm cs_R (aggargs_f ag), m,
                                      ins_pos g y,
                                      UDSince
(dargs cs_R cs_L args, phi_d, psi_d,
  (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))),
  udsx_init (dargs cs_R cs_L args) (dmsk cs_R cs_L))))
                  else UDFail))))
    | n, cs, MUntil (args, phi, psi, buf, nts, t, aux) ->
        (let cs_L = set_cols (args_L args) in
         let cs_R = set_cols (args_R args) in
         let phi_d = udof (dnode_n n args) cs_L phi in
         let psi_d = udof (dnode_n n args) cs_R psi in
          (match args_agg args
            with None ->
              (if equal_nata (args_n args) n &&
                    (equal_lista equal_nat cs cs_R &&
                      (superset equal_nat cs_R cs_L &&
                        (equal_proda
                           (equal_list
                             (equal_set
                               (cenum_list,
                                 (ceq_list (ceq_option ceq_event_data)),
                                 (ccompare_list
                                   (ccompare_option ccompare_event_data)),
                                 (equal_list (equal_option equal_event_data)))))
                           (equal_list
                             (equal_set
                               (cenum_list,
                                 (ceq_list (ceq_option ceq_event_data)),
                                 (ccompare_list
                                   (ccompare_option ccompare_event_data)),
                                 (equal_list (equal_option equal_event_data)))))
                           (map_prod rep_mbuf_t rep_mbuf_t buf) ([], []) &&
                          (null (rep_mbuf_t nts) && equal_nata t zero_nata))))
                then UDUntil
                       (dargs cs cs_L args, dmsk cs cs_L, phi_d, psi_d,
                         (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty, zero_nata,
                         udux_init (dargs cs cs_L args))
                else UDFail)
            | Some ag ->
              (let m = size_lista (aggargs_tys ag) in
               let g = dagg_gcols ag in
               let y = aggargs_y ag in
                (if equal_nata (args_n args) (plus_nata m (aggargs_n ag)) &&
                      (equal_nata (aggargs_n ag) n &&
                        (superset equal_nat cs_R cs_L &&
                          (equal_proda
                             (equal_list
                               (equal_set
                                 (cenum_list,
                                   (ceq_list (ceq_option ceq_event_data)),
                                   (ccompare_list
                                     (ccompare_option ccompare_event_data)),
                                   (equal_list
                                     (equal_option equal_event_data)))))
                             (equal_list
                               (equal_set
                                 (cenum_list,
                                   (ceq_list (ceq_option ceq_event_data)),
                                   (ccompare_list
                                     (ccompare_option ccompare_event_data)),
                                   (equal_list
                                     (equal_option equal_event_data)))))
                             (map_prod rep_mbuf_t rep_mbuf_t buf) ([], []) &&
                            (null (rep_mbuf_t nts) &&
                              (equal_nata t zero_nata &&
                                (equal_lista equal_nat
                                   (upt zero_nata m @
                                     mapa (fun c -> plus_nata c m) g)
                                   cs_R &&
                                  (equal_lista equal_nat cs
                                     (merge_cols g [y]) &&
                                    (sorted_wrt less_nat g &&
                                       list_all (fun c -> less_nat c n) g &&
                                      (less_nat y n &&
(not (membera equal_nat g y) &&
  ((if aggargs_g0 ag then null g else true) &&
    less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
      (fvi_trm zero_nata (aggargs_f ag))
      (set (ceq_nat, ccompare_nat, set_impl_nat) cs_R))))))))))))
                  then UDAgg (aggargs_g0 ag, aggargs_omega ag,
                               reindex_trm cs_R (aggargs_f ag), m, ins_pos g y,
                               UDUntil
                                 (dargs cs_R cs_L args, dmsk cs_R cs_L, phi_d,
                                   psi_d, (mbuf_t_empty, mbuf_t_empty),
                                   mbuf_t_empty, zero_nata,
                                   udux_init (dargs cs_R cs_L args)))
                  else UDFail))))
    | n, cs, MAndAssign (phi, conf) ->
        (let y = fst conf in
         let t = snd conf in
         let cs0 = rem_col cs y in
          (if membera equal_nat cs y &&
                less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                  (fvi_trm zero_nata t)
                  (set (ceq_nat, ccompare_nat, set_impl_nat) cs0)
            then UDAndAssign (ins_pos cs0 y, reindex_trm cs0 t, udof n cs0 phi)
            else UDFail))
    | n, cs, MLet (p, m, phi, psi) ->
        UDLet (p, m, udof m (upt zero_nata m) phi, udof n cs psi)
    | n, cs, MFrz (p, m, phi, psi, jfrz, jpsi0, jphi, alpha_s) ->
        (if null alpha_s
          then UDFrz (p, m, udof m (upt zero_nata m) phi, udof n cs psi, jfrz,
                       jpsi0, jphi, [])
          else UDFail)
    | n, cs, MLetPast (p, m, phi, psi, i, buf) ->
        (if is_none buf
          then UDLetPast
                 (p, m, udof m (upt zero_nata m) phi, udof n cs psi, i, None)
          else UDFail)
    | n, cs, MTrigger (args, phi, psi, buf, nts, aux) ->
        (let cs_L = set_cols (args_L args) in
          (if equal_nata (args_n args) n &&
                (set_eq (cenum_nat, ceq_nat, ccompare_nat) (args_R args)
                   (set (ceq_nat, ccompare_nat, set_impl_nat) cs) &&
                  (superset equal_nat cs cs_L &&
                    (memL (args_ivl args) zero_nata &&
                       memR (args_ivl args) zero_nata &&
                      (equal_proda
                         (equal_list
                           (equal_set
                             (cenum_list,
                               (ceq_list (ceq_option ceq_event_data)),
                               (ccompare_list
                                 (ccompare_option ccompare_event_data)),
                               (equal_list (equal_option equal_event_data)))))
                         (equal_list
                           (equal_set
                             (cenum_list,
                               (ceq_list (ceq_option ceq_event_data)),
                               (ccompare_list
                                 (ccompare_option ccompare_event_data)),
                               (equal_list (equal_option equal_event_data)))))
                         (map_prod rep_mbuf_t rep_mbuf_t buf) ([], []) &&
                        null (rep_mbuf_t nts)))))
            then UDTrigger
                   (dargs cs cs_L args, emb_plan cs cs_L, udof n cs_L phi,
                     udof n cs psi, (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                     ed_init_mmtaux (dargs cs cs_L args))
            else UDFail))
    | n, cs, MTP (mt, i) ->
        (if equal_lista equal_nat cs (mtrm_dcols mt) then UDTP (mt, i)
          else UDFail)
    | n, cs, MTS mt ->
        (if equal_lista equal_nat cs (mtrm_dcols mt) then UDTS mt else UDFail)
    | n, cs, MAndTrigger (v, va, vb, vc, vd, ve, vf, vg, vh) -> UDFail
    | n, cs, MMatchP (v, va, vb, vc, vd, ve, vf) -> UDFail
    | n, cs, MMatchF (v, va, vb, vc, vd, ve, vf, vg) -> UDFail;;

let rec freeze_meval0
  eval k x2 = match eval, k, x2 with eval, k, [] -> ([], [])
    | eval, k, alpha :: alpha_s ->
        (let (ys, _) = eval alpha in
          (match drop k ys with [] -> ([], alpha :: alpha_s)
            | y :: _ ->
              (let (zs, a) = freeze_meval0 eval (suc k) alpha_s in
                (y :: zs, a))));;

let rec comp_fun_commute_apply (Abs_comp_fun_commute x) = x;;

let rec set_fold_cfc (_A1, _A2)
  f b x2 = match f, b, x2 with
    f, b, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold_cfc RBT_set: ccompare = None"
            (fun _ -> set_fold_cfc (_A1, _A2) f b (RBT_set rbt))
        | Some _ -> foldb _A2 (comp_fun_commute_apply f) rbt b)
    | f, b, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold_cfc DList_set: ceq = None"
              (fun _ -> set_fold_cfc (_A1, _A2) f b (DList_set dxs))
          | Some _ -> foldc _A1 (comp_fun_commute_apply f) dxs b)
    | f, b, Set_Monad xs ->
        (match ceq _A1
          with None ->
            failwith "set_fold_cfc Set_Monad: ceq = None"
              (fun _ -> set_fold_cfc (_A1, _A2) f b (Set_Monad xs))
          | Some eq -> fold (comp_fun_commute_apply f) (list_remdups eq xs) b)
    | f, b, Collect_set p ->
        failwith "set_fold_cfc not supported on Collect_set"
          (fun _ -> set_fold_cfc (_A1, _A2) f b (Collect_set p))
    | f, b, Complement a ->
        failwith "set_fold_cfc not supported on Complement"
          (fun _ -> set_fold_cfc (_A1, _A2) f b (Complement a));;

let rec minit_safe_d
  phi = binda (dformula_of true (nfv phi) (upt zero_nata (nfv phi))
                (meinit0 (nfv phi) phi))
          (fun d ->
            (if equal_nata (dfail_nodes d) zero_nata
              then (fun () ->
                     (zero_nata, (zero_nata, (d, (nfv phi, empty_queue)))))
              else failwith
                     "minit_safe_d: the formula is outside the dense fragment"));;

let rec letpast_meval0 (_B1, _B2) _D
  eval j i ys xs p ts db phi =
    (let (ysa, phia) = eval ts (updateb (_B1, _B2) p xs db) phi in
      (if not (equal_nata (size _D phia) (size _D phi))
        then ([], (zero_nata, (None, phi)))
        else (match ysa
               with [] ->
                 (ys @ ysa, (plus_nata i (size_lista xs), (None, phia)))
               | y :: _ ->
                 (if less_eq_nat j (suc (plus_nata i (size_lista xs)))
                   then (ys @ ysa,
                          (plus_nata i (size_lista xs), (Some y, phia)))
                   else letpast_meval0 (_B1, _B2) _D eval j
                          (plus_nata i (size_lista xs)) (ys @ ysa) ysa p []
                          (map_values _B1 (fun _ _ -> []) db) phia))));;

let ed_rbt_fold_table_v :
  (((event_data option) list ->
     ((event_data option) list) set -> ((event_data option) list) set) ->
    (((event_data option) list), unit) mapping_rbt ->
      ((event_data option) list) set -> ((event_data option) list) set)
    boxed
  = Box (foldb (ccompare_list (ccompare_option ccompare_event_data)));;

let rec ed_image
  h x1 = match h, x1 with
    h, RBT_set rbt ->
      unbox ed_rbt_fold_table_v
        (comp (insert
                ((ceq_list (ceq_option ceq_event_data)),
                  (ccompare_list (ccompare_option ccompare_event_data))))
          h)
        rbt ed_bot
    | g, DList_set dxs ->
        foldc (ceq_list (ceq_option ceq_event_data))
          (comp (insert
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data))))
            g)
          dxs ed_bot
    | f, Complement (Complement b) -> ed_image f b
    | f, Collect_set a ->
        failwith "image Collect_set" (fun _ -> ed_image f (Collect_set a))
    | f, Set_Monad xs -> Set_Monad (mapa f xs);;

let rec ed_rbtc_lookup
  x0 k = match x0, k with Empty, k -> None
    | Branch (cc, l, x, y, r), k ->
        (match ed_comparator k x with Eqa -> Some y | Lt -> ed_rbtc_lookup l k
          | Gt -> ed_rbtc_lookup r k);;

let rec ed_rbt_inter_list
  xb xc =
    Mapping_RBTa
      (fold (fun k -> ed_rbtc_insert k ())
        (filtera
          (fun x -> not (is_none (ed_rbtc_lookup (unbox ed_impl_of_v xb) x)))
          xc)
        Empty);;

let rec ed_rbt_meet_unit
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_inter_with_key ed_comparator xc (unbox ed_impl_of_v xd)
        (unbox ed_impl_of_v xe));;

let rec ed_rbt_lookup_unit t k = ed_rbtc_lookup (unbox ed_impl_of_v t) k;;

let rec ed_rbt_member
  t x = equal_optiona equal_unit (ed_rbt_lookup_unit t x) (Some ());;

let rec ed_member
  x xa1 = match x, xa1 with
    x, Set_Monad xs ->
      list_member (equality_list (equality_option equal_event_dataa)) xs x
    | xa, Complement x -> not (ed_member xa x)
    | x, RBT_set rbt -> ed_rbt_member rbt x
    | x, DList_set dxs -> memberc (ceq_list (ceq_option ceq_event_data)) dxs x
    | x, Collect_set a -> a x;;

let rec ed_rbt_join_unit
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_union_with_key ed_comparator xc (unbox ed_impl_of_v xd)
        (unbox ed_impl_of_v xe));;

let rec ed_inter
  g ga = match g, ga with
    RBT_set rbt1, Set_Monad xs -> RBT_set (ed_rbt_inter_list rbt1 xs)
    | Set_Monad xs, RBT_set rbt1 -> RBT_set (ed_rbt_inter_list rbt1 xs)
    | Set_Monad xs, DList_set dxs2 ->
        DList_set
          (filterd (ceq_list (ceq_option ceq_event_data))
            (list_member (equality_list (equality_option equal_event_dataa)) xs)
            dxs2)
    | Set_Monad xs1, Set_Monad xs2 ->
        Set_Monad
          (filtera
            (list_member (equality_list (equality_option equal_event_dataa))
              xs2)
            xs1)
    | RBT_set rbt, DList_set dxs ->
        RBT_set
          (ed_rbt_inter_list rbt
            (list_of_dlist (ceq_list (ceq_option ceq_event_data)) dxs))
    | RBT_set rbt1, RBT_set rbt2 ->
        RBT_set (ed_rbt_meet_unit (fun _ _ -> id) rbt1 rbt2)
    | DList_set dxs1, Set_Monad xs ->
        DList_set
          (filterd (ceq_list (ceq_option ceq_event_data))
            (list_member (equality_list (equality_option equal_event_dataa)) xs)
            dxs1)
    | DList_set dxs1, DList_set dxs2 ->
        DList_set
          (filterd (ceq_list (ceq_option ceq_event_data))
            (memberc (ceq_list (ceq_option ceq_event_data)) dxs2) dxs1)
    | DList_set dxs, RBT_set rbt ->
        RBT_set
          (ed_rbt_inter_list rbt
            (list_of_dlist (ceq_list (ceq_option ceq_event_data)) dxs))
    | Complement ba, Complement b -> Complement (ed_union ba b)
    | g, RBT_set rbt2 ->
        RBT_set
          (filtere (ccompare_list (ccompare_option ccompare_event_data))
            (comp (fun x -> ed_member x g) fst) rbt2)
    | RBT_set rbt1, g ->
        RBT_set
          (filtere (ccompare_list (ccompare_option ccompare_event_data))
            (comp (fun x -> ed_member x g) fst) rbt1)
    | h, DList_set dxs2 ->
        DList_set
          (filterd (ceq_list (ceq_option ceq_event_data))
            (fun x -> ed_member x h) dxs2)
    | DList_set dxs1, h ->
        DList_set
          (filterd (ceq_list (ceq_option ceq_event_data))
            (fun x -> ed_member x h) dxs1)
    | i, Set_Monad xs -> Set_Monad (filtera (fun x -> ed_member x i) xs)
    | Set_Monad xs, i -> Set_Monad (filtera (fun x -> ed_member x i) xs)
    | j, Collect_set a -> Collect_set (fun x -> a x && ed_member x j)
    | Collect_set a, j -> Collect_set (fun x -> a x && ed_member x j)
and ed_union
  ba b = match ba, b with
    ba, Complement b -> Complement (ed_inter (uminus_set ba) b)
    | Complement ba, b -> Complement (ed_inter ba (uminus_set b))
    | RBT_set rbt1, RBT_set rbt2 ->
        RBT_set (ed_rbt_join_unit (fun _ _ -> id) rbt1 rbt2)
    | RBT_set rbt, DList_set dxs ->
        RBT_set
          (foldc (ceq_list (ceq_option ceq_event_data))
            (fun k -> ed_rbt_insert k ()) dxs rbt)
    | DList_set dxs, RBT_set rbt ->
        RBT_set
          (foldc (ceq_list (ceq_option ceq_event_data))
            (fun k -> ed_rbt_insert k ()) dxs rbt)
    | DList_set dxs1, DList_set dxs2 ->
        DList_set (union (ceq_list (ceq_option ceq_event_data)) dxs1 dxs2)
    | Set_Monad zs, RBT_set rbt2 ->
        RBT_set (fold (fun k -> ed_rbt_insert k ()) zs rbt2)
    | RBT_set rbt1, Set_Monad zs ->
        RBT_set (fold (fun k -> ed_rbt_insert k ()) zs rbt1)
    | Set_Monad ws, DList_set dxs2 ->
        DList_set
          (fold (inserta (ceq_list (ceq_option ceq_event_data))) ws dxs2)
    | DList_set dxs1, Set_Monad ws ->
        DList_set
          (fold (inserta (ceq_list (ceq_option ceq_event_data))) ws dxs1)
    | Set_Monad xs, Set_Monad ys -> Set_Monad (xs @ ys)
    | b, Collect_set a -> Collect_set (fun x -> a x || ed_member x b)
    | Collect_set a, b -> Collect_set (fun x -> a x || ed_member x b);;

let rec dannotate
  i tq x2 acc = match i, tq, x2, acc with i, tq, [], acc -> (i, (tq, rev acc))
    | i, tq, v :: vs, acc ->
        (match mbuf_t_cases tq
          with (None, tqa) ->
            (plus_nata (plus_nata i one_nata) (size_lista vs), (tqa, rev acc))
          | (Some t, tqa) ->
            dannotate (plus_nata i one_nata) tqa vs ((i, (t, v)) :: acc));;

let rec proj_tuple x0 x1 = match x0, x1 with [], [] -> []
                     | true :: bs, a :: asa -> a :: proj_tuple bs asa
                     | false :: bs, a :: asa -> None :: proj_tuple bs asa
                     | b :: bs, [] -> []
                     | [], a :: asa -> [];;

let rec ed_proj_tuple_in_join
  pos bs asa t =
    (if pos then ed_member (proj_tuple bs asa) t
      else not (ed_member (proj_tuple bs asa) t));;

let ed_upd_set_nat_v :
  ((((event_data option) list), nat) mapping ->
    ((event_data option) list -> nat) ->
      ((event_data option) list) set ->
        (((event_data option) list), nat) mapping)
    boxed
  = Box (upd_set
          (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
            (ccompare_list (ccompare_option ccompare_event_data)),
            (equal_list (equal_option equal_event_data))));;

let ed_mfilter_nat_v :
  (((event_data option) list -> nat -> bool) ->
    (((event_data option) list), nat) mapping ->
      (((event_data option) list), nat) mapping)
    boxed
  = Box (filterc (ccompare_list (ccompare_option ccompare_event_data)));;

let rec proj_tuple_in_join (_A1, _A2)
  pos bs asa t =
    (if pos
      then member
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             (proj_tuple bs asa) t
      else not (member
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)))
                 (proj_tuple bs asa) t));;

let rec proj_tuple_in_join_optim (_A1, _A2)
  pos r maskR l maskL =
    (if equal_lista equal_bool maskL maskR
      then (if pos
             then inf_seta
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                    r l
             else minus_set
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                    r l)
      else (if list_all not maskL
             then (let nones = replicate (size_lista maskL) None in
                    (if equal_boola pos
                          (member
                            ((ceq_list (ceq_option _A1)),
                              (ccompare_list (ccompare_option _A2)))
                            nones l)
                      then r
                      else set_empty
                             ((ceq_list (ceq_option _A1)),
                               (ccompare_list (ccompare_option _A2)))
                             (of_phantom set_impl_lista)))
             else filter
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                    (fun asa -> proj_tuple_in_join (_A1, _A2) pos maskL asa l)
                    r));;

let rec update_mmtaux (_A1, _A2, _A3)
  args nt idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once
    tuple_in_once_keys tuple_since_hist hist_sat since_sat =
    (let (_, (data_preva, (move, (tuple_in_oncea, tuple_in_once_keysa)))) =
       shift_end
         ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
           (equal_list (equal_option _A3)))
         (flip_int_less_lower (args_ivl args)) nt fst
         (empty_queue, (data_prev, (tuple_in_once, tuple_in_once_keys)))
       in
     let move_len = size_lista move in
     let idx_mida = plus_nata idx_mid move_len in
     let (data_ina, drop) =
       takedropWhile_queue
         (fun (t, _) -> not (memR (args_ivl args) (minus_nata nt t))) data_in
       in
     let movea =
       filtera (fun (t, _) -> memR (args_ivl args) (minus_nata nt t)) move in
     let drop_prev_len = minus_nata move_len (size_lista movea) in
     let idx_oldesta =
       plus_nata (plus_nata idx_oldest (size_lista drop)) drop_prev_len in
     let data_inb = fold (fun (t, (_, r)) -> append_queue (t, r)) movea data_ina
       in
     let (tuple_since_hista, (hist_sata, (_, since_sata))) =
       fold (fun (_, (l, r))
              (tuple_since_hista, (hist_sata, (idx_move, since_sata))) ->
              (let tuple_since_histb =
                 filterc (ccompare_list (ccompare_option _A2))
                   (fun asa _ ->
                     member
                       ((ceq_list (ceq_option _A1)),
                         (ccompare_list (ccompare_option _A2)))
                       asa r)
                   tuple_since_hista
                 in
               let hist_satb =
                 inf_seta
                   ((ceq_list (ceq_option _A1)),
                     (ccompare_list (ccompare_option _A2)))
                   hist_sata r
                 in
               let since_satb =
                 inf_seta
                   ((ceq_list (ceq_option _A1)),
                     (ccompare_list (ccompare_option _A2)))
                   since_sata r
                 in
                (upd_set
                   (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                     (ccompare_list (ccompare_option _A2)),
                     (equal_list (equal_option _A3)))
                   tuple_since_histb (fun _ -> idx_move)
                   (filter
                     ((ceq_list (ceq_option _A1)),
                       (ccompare_list (ccompare_option _A2)))
                     (fun k ->
                       is_none
                         (lookupa
                           ((ccompare_list (ccompare_option _A2)),
                             (equal_list (equal_option _A3)))
                           tuple_since_histb k))
                     r),
                  (hist_satb,
                    (plus_nata idx_move one_nata,
                      sup_seta
                        ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)))
                        since_satb
                        (proj_tuple_in_join_optim (_A1, _A2) (args_pos args) r
                          (join_mask (args_n args) (args_R args)) l
                          (join_mask (args_n args) (args_L args))))))))
         move (tuple_since_hist, (hist_sat, (idx_mid, since_sat)))
       in
     let tuple_since_histb =
       (if equal_nata idx_mida idx_oldesta
         then mapping_empty (ccompare_list (ccompare_option _A2))
                (of_phantom mapping_impl_lista)
         else tuple_since_hista)
       in
     let since_satb =
       (if equal_nata idx_mida idx_oldesta
         then set_empty
                ((ceq_list (ceq_option _A1)),
                  (ccompare_list (ccompare_option _A2)))
                (of_phantom set_impl_lista)
         else since_sata)
       in
     let hist_satb =
       (match fst (safe_hd data_inb)
         with None ->
           set_empty
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             (of_phantom set_impl_lista)
         | Some db ->
           sup_seta
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             hist_sata
             (filter
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)))
               (fun tuple ->
                 (match
                   lookupa
                     ((ccompare_list (ccompare_option _A2)),
                       (equal_list (equal_option _A3)))
                     tuple_since_histb tuple
                   with None -> false
                   | Some idx -> less_eq_nat idx idx_oldesta))
               (snd db)))
       in
      (idx_mida,
        (idx_oldesta,
          (data_preva,
            (data_inb,
              (tuple_in_oncea,
                (tuple_in_once_keysa,
                  (tuple_since_histb, (hist_satb, since_satb)))))))));;

let ed_impl_of_nat_v :
  ((((event_data option) list), nat) mapping_rbt ->
    (((event_data option) list), nat) rbt)
    boxed
  = Box (impl_ofa (ccompare_list (ccompare_option ccompare_event_data)));;

let rec ed_rbt_lookup_nat t k = ed_rbtc_lookup (unbox ed_impl_of_nat_v t) k;;

let rec ed_lookup_nat
  = function RBT_Mapping t -> ed_rbt_lookup_nat t
    | Assoc_List_Mapping al ->
        lookup (equal_list (equal_option equal_event_data)) al;;

let rec ed_filter p a = ed_inter a (Collect_set p);;

let rec ed_update_mmtaux
  args nt l r =
    (fun (_, (idx_next,
               (idx_mid,
                 (idx_oldest,
                   (maskL,
                     (maskR,
                       (data_prev,
                         (data_in,
                           (tuple_in_once,
                             (tuple_in_once_keys,
                               (tuple_since_hist,
                                 (hist_sat, since_sat))))))))))))
      -> (let (idx_mida,
                (idx_oldesta,
                  (data_preva,
                    (data_ina,
                      (tuple_in_oncea,
                        (tuple_in_once_keysa,
                          (tuple_since_hista, (hist_sata, since_sata))))))))
            = update_mmtaux
                (ceq_event_data, ccompare_event_data, equal_event_data) args nt
                idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once
                tuple_in_once_keys tuple_since_hist hist_sat since_sat
            in
           (if memL (args_ivl args) zero_nata && memR (args_ivl args) zero_nata
             then (let tuple_since_histb =
                     unbox ed_mfilter_nat_v (fun asa _ -> ed_member asa r)
                       tuple_since_hista
                     in
                    (nt, (plus_nata idx_next one_nata,
                           (plus_nata idx_mida one_nata,
                             (idx_oldesta,
                               (maskL,
                                 (maskR,
                                   (data_preva,
                                     (append_queue (nt, r) data_ina,
                                       (tuple_in_oncea,
 (tuple_in_once_keysa,
   (unbox ed_upd_set_nat_v tuple_since_histb (fun _ -> idx_mida)
      (ed_filter (fun k -> is_none (ed_lookup_nat tuple_since_histb k)) r),
     ((if is_emptya data_ina then r else ed_inter hist_sata r),
       ed_union (ed_inter since_sata r)
         (ed_filter
           (fun asa -> ed_proj_tuple_in_join (args_pos args) maskL asa l)
           r))))))))))))))
             else (nt, (plus_nata idx_next one_nata,
                         (idx_mida,
                           (idx_oldesta,
                             (maskL,
                               (maskR,
                                 (append_queue (nt, (l, r)) data_preva,
                                   (data_ina,
                                     (unbox ed_upd_set_nat_v tuple_in_oncea
(fun _ -> nt) l,
                                       (ed_union tuple_in_once_keysa l,
 (tuple_since_hista, (hist_sata, since_sata)))))))))))))));;

let rec de_gcnt_add1
  t cc =
    (let (c, s) = cc in
      (match edl_lookup_nat c t
        with None -> (edl_update_nat t one_nata c, edl_insert t s)
        | Some k -> (edl_update_nat t (plus_nata k one_nata) c, s)));;

let rec de_gcnt_add
  t cc =
    fold de_gcnt_add1
      (csl (finite_UNIV_list, (ceq_list ceq_event_data),
             (ccompare_list ccompare_event_data))
        t)
      cc;;

let rec de_gsw_add_new_table
  args x aux =
    (let (t, (pend, (win, cc))) = aux in
      (if memL (args_ivl args) zero_nata
        then (t, (pend, (append_queue (t, x) win, de_gcnt_add x cc)))
        else (t, (append_queue (t, x) pend, (win, cc)))));;

let ed_fold_cfc_agg5_v :
  ((((event_data option) list),
     (bool * (((event_data option) list), list_aux) mapping))
     comp_fun_commute ->
    bool * (((event_data option) list), list_aux) mapping ->
      ((event_data option) list) set ->
        bool * (((event_data option) list), list_aux) mapping)
    boxed
  = Box (set_fold_cfc
          ((ceq_list (ceq_option ceq_event_data)),
            (ccompare_list (ccompare_option ccompare_event_data))));;

let ed_fold_cfc_agg4_v :
  ((((event_data option) list),
     (bool * (((event_data option) list), (nat * Z.t)) mapping))
     comp_fun_commute ->
    bool * (((event_data option) list), (nat * Z.t)) mapping ->
      ((event_data option) list) set ->
        bool * (((event_data option) list), (nat * Z.t)) mapping)
    boxed
  = Box (set_fold_cfc
          ((ceq_list (ceq_option ceq_event_data)),
            (ccompare_list (ccompare_option ccompare_event_data))));;

let ed_fold_cfc_agg3_v :
  ((((event_data option) list),
     (bool * (((event_data option) list), nat) mapping))
     comp_fun_commute ->
    bool * (((event_data option) list), nat) mapping ->
      ((event_data option) list) set ->
        bool * (((event_data option) list), nat) mapping)
    boxed
  = Box (set_fold_cfc
          ((ceq_list (ceq_option ceq_event_data)),
            (ccompare_list (ccompare_option ccompare_event_data))));;

let ed_impl_of_rank_v :
  ((((event_data option) list), list_aux) mapping_rbt ->
    (((event_data option) list), list_aux) rbt)
    boxed
  = Box (impl_ofa (ccompare_list (ccompare_option ccompare_event_data)));;

let rec ed_rbt_insert_rank
  xc xd xe = Mapping_RBTa (ed_rbtc_insert xc xd (unbox ed_impl_of_rank_v xe));;

let rec ed_update_rank
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t -> RBT_Mapping (ed_rbt_insert_rank k v t)
    | k, v, Assoc_List_Mapping al ->
        Assoc_List_Mapping
          (updatea (equal_list (equal_option equal_event_data)) k v al)
    | k, v, Mapping m ->
        Mapping
          (fun_upd (equal_list (equal_option equal_event_data)) m k (Some v));;

let rec ed_rbt_lookup_rank t k = ed_rbtc_lookup (unbox ed_impl_of_rank_v t) k;;

let rec ed_lookup_rank
  = function RBT_Mapping t -> ed_rbt_lookup_rank t
    | Assoc_List_Mapping al ->
        lookup (equal_list (equal_option equal_event_data)) al;;

let rec insert_rank
  args typea t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                let (new_v, new_list) =
                  (match (ed_lookup_rank m group, (term, typea))
                    with (None, (EInt terma, IntT)) ->
                      (true,
                        LInt (insert_treelist (equal_integer, linorder_integer)
                               terma (empty_treelist linorder_integer)))
                    | (None, (EInt _, StringT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EString _, IntT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EString terma, StringT)) ->
                      (true,
                        LString
                          (insert_treelist (equal_string8, linorder_string8)
                            terma (empty_treelist linorder_string8)))
                    | (Some (LInt ta), (EInt terma, IntT)) ->
                      (true,
                        LInt (insert_treelist (equal_integer, linorder_integer)
                               terma ta))
                    | (Some (LInt _), (EInt _, StringT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LInt _), (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LInt _), (EString _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EInt _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EString _, IntT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString ta), (EString terma, StringT)) ->
                      (true,
                        LString
                          (insert_treelist (equal_string8, linorder_string8)
                            terma ta)))
                  in
                 (new_v,
                   (if new_v then ed_update_rank group new_list m
                     else ed_mempty_rank)))
      else (v, m));;

let rec insert_rank_cfc xb xc = Abs_comp_fun_commute (insert_rank xb xc);;

let ed_impl_of_sum_v :
  ((((event_data option) list), (nat * Z.t)) mapping_rbt ->
    (((event_data option) list), (nat * Z.t)) rbt)
    boxed
  = Box (impl_ofa (ccompare_list (ccompare_option ccompare_event_data)));;

let rec ed_rbt_insert_sum
  xc xd xe = Mapping_RBTa (ed_rbtc_insert xc xd (unbox ed_impl_of_sum_v xe));;

let rec ed_update_sum
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t -> RBT_Mapping (ed_rbt_insert_sum k v t)
    | k, v, Assoc_List_Mapping al ->
        Assoc_List_Mapping
          (updatea (equal_list (equal_option equal_event_data)) k v al)
    | k, v, Mapping m ->
        Mapping
          (fun_upd (equal_list (equal_option equal_event_data)) m k (Some v));;

let rec ed_rbt_lookup_sum t k = ed_rbtc_lookup (unbox ed_impl_of_sum_v t) k;;

let rec ed_lookup_sum
  = function RBT_Mapping t -> ed_rbt_lookup_sum t
    | Assoc_List_Mapping al ->
        lookup (equal_list (equal_option equal_event_data)) al;;

let rec insert_sum
  args t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                 (match (ed_lookup_sum m group, term)
                   with (None, EInt i) ->
                     (true, ed_update_sum group (one_nata, i) m)
                   | (None, EFloat _) -> (false, ed_mempty_sum)
                   | (None, EString _) -> (false, ed_mempty_sum)
                   | (Some (cnt, agg_sum), EInt i) ->
                     (true,
                       ed_update_sum group
                         (plus_nata cnt one_nata, Z.add agg_sum i) m)
                   | (Some (_, _), EFloat _) -> (false, ed_mempty_sum)
                   | (Some (_, _), EString _) -> (false, ed_mempty_sum)))
      else (v, m));;

let rec insert_sum_cfc xa = Abs_comp_fun_commute (insert_sum xa);;

let rec ed_rbt_insert_nat
  xc xd xe = Mapping_RBTa (ed_rbtc_insert xc xd (unbox ed_impl_of_nat_v xe));;

let rec ed_update_nat
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t -> RBT_Mapping (ed_rbt_insert_nat k v t)
    | k, v, Assoc_List_Mapping al ->
        Assoc_List_Mapping
          (updatea (equal_list (equal_option equal_event_data)) k v al)
    | k, v, Mapping m ->
        Mapping
          (fun_upd (equal_list (equal_option equal_event_data)) m k (Some v));;

let rec insert_cnt
  args t (v, m) =
    (if v then (v, (let group = drop (size_lista (aggargs_tys args)) t in
                     (match ed_lookup_nat m group
                       with None -> ed_update_nat group one_nata m
                       | Some i ->
                         ed_update_nat group (plus_nata i one_nata) m)))
      else (v, m));;

let rec insert_cnt_cfc xa = Abs_comp_fun_commute (insert_cnt xa);;

let rec insert_maggaux
  args data aux =
    (match aux
      with CntAux m ->
        (let (v, ma) =
           unbox ed_fold_cfc_agg3_v (insert_cnt_cfc args) (true, m) data in
          (v, CntAux ma))
      | SumAux m ->
        (let (v, ma) =
           unbox ed_fold_cfc_agg4_v (insert_sum_cfc args) (true, m) data in
          (v, SumAux ma))
      | RankAux (m, t) ->
        (let (v, ma) =
           unbox ed_fold_cfc_agg5_v (insert_rank_cfc args t) (true, m) data in
          (v, RankAux (ma, t))));;

let ed_finite_v : (((event_data option) list) set -> bool) boxed
  = Box (finite
          (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
            (ccompare_list (ccompare_option ccompare_event_data))));;

let rec insert_maggauxa
  args x xa2 = match args, x, xa2 with args, x, None -> None
    | args, x, Some aux ->
        (let (v, auxa) = insert_maggaux args x aux in
          (if v && unbox ed_finite_v x then Some auxa else None));;

let rec edl_image_to_wide
  h (RBT_set rbt) =
    foldb (ccompare_list ccompare_event_data) (fun x -> ed_insert (h x)) rbt
      ed_bot;;

let rec udwiden x0 xs = match x0, xs with [], xs -> []
                  | false :: bs, xs -> None :: udwiden bs xs
                  | true :: bs, x :: xs -> Some x :: udwiden bs xs
                  | true :: bs, [] -> [];;

let rec de_udtabw n cs d = edl_image_to_wide (udwiden (wide_mask n cs)) d;;

let rec udagg_wide p w d = de_udtabw (suc w) (dagg_ccols p w) d;;

let rec uag_ins
  p w t cc ax =
    insert_maggauxa (dagg_args p w) (udagg_wide p w (edl_minus t (snd cc))) ax;;

let rec usa_add_new_table
  args p x aux =
    (let ((t, (pend, (win, cc))), ax) = aux in
      (if memL (args_ivl args) zero_nata
        then ((t, (pend, (append_queue (t, x) win, de_gcnt_add x cc))),
               uag_ins p (args_n args) x cc ax)
        else ((t, (append_queue (t, x) pend, (win, cc))), ax)));;

let rec udsx_add_new_table
  args x xa2 = match args, x, xa2 with
    args, x, UDSX_gen d -> UDSX_gen (de_gadd_new_table_msaux args x d)
    | args, x, UDSX_win w -> UDSX_win (de_gsw_add_new_table args x w)
    | args, x, UDSX_wagg (p, a) -> UDSX_wagg (p, usa_add_new_table args p x a);;

let rec de_gcnt_del1
  t cc =
    (let (c, s) = cc in
      (match edl_lookup_nat c t with None -> (c, s)
        | Some k ->
          (if less_eq_nat k one_nata
            then (edl_delete_nat t c, unbox edl_remove_v t s)
            else (edl_update_nat t (minus_nata k one_nata) c, s))));;

let rec de_gcnt_del
  t cc =
    fold de_gcnt_del1
      (csl (finite_UNIV_list, (ceq_list ceq_event_data),
             (ccompare_list ccompare_event_data))
        t)
      cc;;

let rec de_gsw_expire
  args nt win cc =
    (match safe_hd win with (None, wina) -> (wina, cc)
      | (Some e, wina) ->
        (if memR (args_ivl args) (minus_nata nt (fst e)) then (wina, cc)
          else de_gsw_expire args nt (tl_queue wina)
                 (de_gcnt_del (snd e) cc)));;

let rec de_gsw_move
  args nt pend win cc =
    (match safe_hd pend with (None, penda) -> (penda, (win, cc))
      | (Some e, penda) ->
        (if memL (args_ivl args) (minus_nata nt (fst e))
          then (if memR (args_ivl args) (minus_nata nt (fst e))
                 then de_gsw_move args nt (tl_queue penda) (append_queue e win)
                        (de_gcnt_add (snd e) cc)
                 else de_gsw_move args nt (tl_queue penda) win cc)
          else (penda, (win, cc))));;

let rec de_gsw_add_new_ts
  args nt aux =
    (let (_, (pend, (win, cc))) = aux in
     let (penda, (wina, cca)) = de_gsw_move args nt pend win cc in
     let (winb, ccb) = de_gsw_expire args nt wina cca in
      (nt, (penda, (winb, ccb))));;

let rec ed_rbtc_del
  x xa1 = match x, xa1 with x, Empty -> Empty
    | x, Branch (cc, a, y, s, b) ->
        (match ed_comparator x y with Eqa -> combinea a b
          | Lt -> ed_rbtc_del_from_left x a y s b
          | Gt -> ed_rbtc_del_from_right x a y s b)
and ed_rbtc_del_from_left
  x xa1 y s b = match x, xa1, y, s, b with
    x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (ed_rbtc_del x (Branch (B, lt, z, v, rt))) y s b
    | x, Empty, y, s, b -> Branch (R, ed_rbtc_del x Empty, y, s, b)
    | x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, ed_rbtc_del x (Branch (R, va, vb, vc, vd)), y, s, b)
and ed_rbtc_del_from_right
  x a y s xa4 = match x, a, y, s, xa4 with
    x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (ed_rbtc_del x (Branch (B, lt, z, v, rt)))
    | x, a, y, s, Empty -> Branch (R, a, y, s, ed_rbtc_del x Empty)
    | x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, ed_rbtc_del x (Branch (R, va, vb, vc, vd)));;

let rec ed_rbtc_delete k t = paint B (ed_rbtc_del k t);;

let rec ed_rbt_delete_rank
  xb xc = Mapping_RBTa (ed_rbtc_delete xb (unbox ed_impl_of_rank_v xc));;

let rec ed_delete_rank
  k x1 = match k, x1 with
    k, RBT_Mapping t -> RBT_Mapping (ed_rbt_delete_rank k t)
    | k, Assoc_List_Mapping al ->
        Assoc_List_Mapping
          (deletea (equal_list (equal_option equal_event_data)) k al)
    | k, Mapping m ->
        Mapping
          (fun_upd (equal_list (equal_option equal_event_data)) m k None);;

let rec delete_rank
  args typea t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                let (a, b) =
                  (match (ed_lookup_rank m group, (term, typea))
                    with (None, (EInt _, IntT)) -> (true, m)
                    | (None, (EInt _, StringT)) -> (false, ed_mempty_rank)
                    | (None, (EFloat _, _)) -> (false, ed_mempty_rank)
                    | (None, (EString _, IntT)) -> (false, ed_mempty_rank)
                    | (None, (EString _, StringT)) -> (true, m)
                    | (Some (LInt ta), (EInt terma, IntT)) ->
                      (true,
                        (let l =
                           remove_treelist (equal_integer, linorder_integer)
                             terma ta
                           in
                          (if equal_treelist (equal_integer, linorder_integer) l
                                (empty_treelist linorder_integer)
                            then ed_delete_rank group m
                            else ed_update_rank group (LInt l) m)))
                    | (Some (LInt _), (EInt _, StringT)) ->
                      (false, ed_mempty_rank)
                    | (Some (LInt _), (EFloat _, _)) -> (false, ed_mempty_rank)
                    | (Some (LInt _), (EString _, _)) -> (false, ed_mempty_rank)
                    | (Some (LString _), (EInt _, _)) -> (false, ed_mempty_rank)
                    | (Some (LString _), (EFloat _, _)) ->
                      (false, ed_mempty_rank)
                    | (Some (LString _), (EString _, IntT)) ->
                      (false, ed_mempty_rank)
                    | (Some (LString ta), (EString terma, StringT)) ->
                      (true,
                        (let l =
                           remove_treelist (equal_string8, linorder_string8)
                             terma ta
                           in
                          (if equal_treelist (equal_string8, linorder_string8) l
                                (empty_treelist linorder_string8)
                            then ed_delete_rank group m
                            else ed_update_rank group (LString l) m))))
                  in
                 (a, b))
      else (v, m));;

let rec delete_rank_cfc xb xc = Abs_comp_fun_commute (delete_rank xb xc);;

let rec ed_rbt_delete_sum
  xb xc = Mapping_RBTa (ed_rbtc_delete xb (unbox ed_impl_of_sum_v xc));;

let rec ed_delete_sum
  k x1 = match k, x1 with
    k, RBT_Mapping t -> RBT_Mapping (ed_rbt_delete_sum k t)
    | k, Assoc_List_Mapping al ->
        Assoc_List_Mapping
          (deletea (equal_list (equal_option equal_event_data)) k al)
    | k, Mapping m ->
        Mapping
          (fun_upd (equal_list (equal_option equal_event_data)) m k None);;

let rec delete_sum
  args t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                 (match (ed_lookup_sum m group, term)
                   with (None, _) -> (false, ed_mempty_sum)
                   | (Some (cnt, agg_sum), EInt i) ->
                     (true,
                       (if equal_nata cnt one_nata then ed_delete_sum group m
                         else ed_update_sum group
                                (minus_nata cnt one_nata, Z.sub agg_sum i) m))
                   | (Some (_, _), EFloat _) -> (false, ed_mempty_sum)
                   | (Some (_, _), EString _) -> (false, ed_mempty_sum)))
      else (v, m));;

let rec delete_sum_cfc xa = Abs_comp_fun_commute (delete_sum xa);;

let rec ed_rbt_delete_nat
  xb xc = Mapping_RBTa (ed_rbtc_delete xb (unbox ed_impl_of_nat_v xc));;

let rec ed_delete_nat
  k x1 = match k, x1 with
    k, RBT_Mapping t -> RBT_Mapping (ed_rbt_delete_nat k t)
    | k, Assoc_List_Mapping al ->
        Assoc_List_Mapping
          (deletea (equal_list (equal_option equal_event_data)) k al)
    | k, Mapping m ->
        Mapping
          (fun_upd (equal_list (equal_option equal_event_data)) m k None);;

let rec delete_cnt
  args t (v, m) =
    (if v then (v, (let group = drop (size_lista (aggargs_tys args)) t in
                     (match ed_lookup_nat m group with None -> m
                       | Some i ->
                         (if equal_nata i one_nata then ed_delete_nat group m
                           else ed_update_nat group (minus_nata i one_nata)
                                  m))))
      else (v, m));;

let rec delete_cnt_cfc xa = Abs_comp_fun_commute (delete_cnt xa);;

let rec delete_maggaux
  args data aux =
    (match aux
      with CntAux m ->
        (let (v, ma) =
           unbox ed_fold_cfc_agg3_v (delete_cnt_cfc args) (true, m) data in
          (v, CntAux ma))
      | SumAux m ->
        (let (v, ma) =
           unbox ed_fold_cfc_agg4_v (delete_sum_cfc args) (true, m) data in
          (v, SumAux ma))
      | RankAux (m, t) ->
        (let (v, ma) =
           unbox ed_fold_cfc_agg5_v (delete_rank_cfc args t) (true, m) data in
          (v, RankAux (ma, t))));;

let rec delete_maggauxa
  args x xa2 = match args, x, xa2 with args, x, None -> None
    | args, x, Some aux ->
        (match delete_maggaux args x aux with (true, auxa) -> Some auxa
          | (false, _) -> None);;

let rec uag_del
  p w t cc ax =
    delete_maggauxa (dagg_args p w)
      (udagg_wide p w
        (edl_filter
          (fun x ->
            equal_optiona equal_nat (edl_lookup_nat (fst cc) x) (Some one_nata))
          t))
      ax;;

let rec usa_expire
  args p nt win cc ax =
    (match safe_hd win with (None, wina) -> (wina, (cc, ax))
      | (Some e, wina) ->
        (if memR (args_ivl args) (minus_nata nt (fst e)) then (wina, (cc, ax))
          else usa_expire args p nt (tl_queue wina) (de_gcnt_del (snd e) cc)
                 (uag_del p (args_n args) (snd e) cc ax)));;

let rec usa_move
  args p nt pend win cc ax =
    (match safe_hd pend with (None, penda) -> (penda, (win, (cc, ax)))
      | (Some e, penda) ->
        (if memL (args_ivl args) (minus_nata nt (fst e))
          then (if memR (args_ivl args) (minus_nata nt (fst e))
                 then usa_move args p nt (tl_queue penda) (append_queue e win)
                        (de_gcnt_add (snd e) cc)
                        (uag_ins p (args_n args) (snd e) cc ax)
                 else usa_move args p nt (tl_queue penda) win cc ax)
          else (penda, (win, (cc, ax)))));;

let rec usa_add_new_ts
  args p nt aux =
    (let ((_, (pend, (win, cc))), ax) = aux in
     let (penda, (wina, (cca, axa))) = usa_move args p nt pend win cc ax in
     let (winb, (ccb, a)) = usa_expire args p nt wina cca axa in
      ((nt, (penda, (winb, ccb))), a));;

let rec udsx_add_new_ts
  args nt x2 = match args, nt, x2 with
    args, nt, UDSX_gen d -> UDSX_gen (de_gadd_new_ts_msaux args nt d)
    | args, nt, UDSX_win w -> UDSX_win (de_gsw_add_new_ts args nt w)
    | args, nt, UDSX_wagg (p, a) -> UDSX_wagg (p, usa_add_new_ts args p nt a);;

let rec de_gsw_result args aux = (let (_, (_, (_, a))) = aux in snd a);;

let rec ed_get_map_result
  m y f =
    ed_image
      (fun k ->
        (match
          lookupa
            ((ccompare_list (ccompare_option ccompare_event_data)),
              (equal_list (equal_option equal_event_data)))
            m k
          with None -> k | Some i -> list_update k y (Some (f i))))
      (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
              (ccompare_list (ccompare_option ccompare_event_data)),
              set_impl_list)
        m);;

let ed_keys_rank_v :
  ((((event_data option) list), list_aux) mapping ->
    ((event_data option) list) set)
    boxed
  = Box (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                (ccompare_list (ccompare_option ccompare_event_data)),
                set_impl_list));;

let ed_keys_sum_v :
  ((((event_data option) list), (nat * Z.t)) mapping ->
    ((event_data option) list) set)
    boxed
  = Box (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                (ccompare_list (ccompare_option ccompare_event_data)),
                set_impl_list));;

let ed_keys_nat_v :
  ((((event_data option) list), nat) mapping -> ((event_data option) list) set)
    boxed
  = Box (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                (ccompare_list (ccompare_option ccompare_event_data)),
                set_impl_list));;

let ed_set_eq_v :
  (((event_data option) list) set -> ((event_data option) list) set -> bool)
    boxed
  = Box (set_eq
          (cenum_list, (ceq_list (ceq_option ceq_event_data)),
            (ccompare_list (ccompare_option ccompare_event_data))));;

let rec result_maggaux
  (Aggargs_ext (cols, n, g0, y, omega, tys, f, ())) aux =
    (match aux
      with CntAux m ->
        (if g0 && unbox ed_set_eq_v (unbox ed_keys_nat_v m) ed_bot
          then ed_singleton_table n y
                 (eval_agg_op omega
                   (set_empty
                     ((ceq_prod ceq_event_data ceq_enat),
                       (ccompare_prod ccompare_event_data ccompare_enat))
                     (of_phantom
                       (set_impl_proda set_impl_event_data set_impl_enat))))
          else ed_get_map_result m y
                 (fun x -> EInt (integer_of_int (int_of_nat x))))
      | SumAux m ->
        (if g0 && unbox ed_set_eq_v (unbox ed_keys_sum_v m) ed_bot
          then ed_singleton_table n y
                 (eval_agg_op omega
                   (set_empty
                     ((ceq_prod ceq_event_data ceq_enat),
                       (ccompare_prod ccompare_event_data ccompare_enat))
                     (of_phantom
                       (set_impl_proda set_impl_event_data set_impl_enat))))
          else (match fst omega
                 with Agg_Sum -> ed_get_map_result m y (fun k -> EInt (snd k))
                 | Agg_Avg ->
                   ed_get_map_result m y
                     (fun x ->
                       EFloat
                         (Stdlib.(/.)
                           (double_of_event_data
                             (EInt (snd (let (xa, a) = x in
  (int_of_nat xa, a)))))
                           (double_of_int
                             (fst (let (xa, a) = x in (int_of_nat xa, a))))))))
      | RankAux (m, _) ->
        (if g0 && unbox ed_set_eq_v (unbox ed_keys_rank_v m) ed_bot
          then ed_singleton_table n y
                 (eval_agg_op omega
                   (set_empty
                     ((ceq_prod ceq_event_data ceq_enat),
                       (ccompare_prod ccompare_event_data ccompare_enat))
                     (of_phantom
                       (set_impl_proda set_impl_event_data set_impl_enat))))
          else (match fst omega
                 with Agg_Min ->
                   ed_get_map_result m y (fun k -> get_edata_list k zero_nata)
                 | Agg_Max ->
                   ed_get_map_result m y
                     (fun k ->
                       get_edata_list k (minus_nata (get_length k) one_nata))
                 | Agg_Med ->
                   ed_get_map_result m y
                     (fun k ->
                       (let u = get_length k in
                        let ua = divide_nata u (nat_of_integer (Z.of_int 2)) in
                        let a =
                          (if dvd (equal_nat, semidom_modulo_nat)
                                (nat_of_integer (Z.of_int 2)) u
                            then Stdlib.(/.)
                                   (Stdlib.(+.)
                                     (double_of_event_data_agg
                                       (get_edata_list k
 (minus_nata ua one_nata)))
                                     (double_of_event_data_agg
                                       (get_edata_list k ua)))
                                   (double_of_int (Int_of_integer (Z.of_int 2)))
                            else double_of_event_data_agg (get_edata_list k ua))
                          in
                         EFloat a)))));;

let rec udagg_p (g0, (omega, (f, (k, pos)))) = uagg g0 omega f k pos;;

let rec uag_res
  p w cc ax =
    (match ax with None -> udagg_p p (snd cc)
      | Some a ->
        (let args = dagg_args p w in
         let msk = wide_mask (aggargs_n args) (upt zero_nata (aggargs_n args))
           in
          edl_image_of_wide (fun x -> deopt (dproj msk x))
            (result_maggaux args a)));;

let rec usa_result
  args p aux =
    (let ((_, (_, (_, cc))), ax) = aux in uag_res p (args_n args) cc ax);;

let rec udsx_result
  args x1 = match args, x1 with args, UDSX_gen d -> de_gresult_msaux args d
    | args, UDSX_win w -> de_gsw_result args w
    | args, UDSX_wagg (p, a) -> usa_result args p a;;

let rec de_gsw_join
  args x aux =
    (let (t, (_, (_, _))) = aux in
      (if (if args_pos args then not (unbox edl_is_empty_v x)
            else unbox edl_is_empty_v x)
        then aux
        else (t, (empty_queue, (empty_queue, (edl_mempty_nat, edl_bot))))));;

let rec usa_join
  args p x aux =
    (let (w, ax) = aux in
      (de_gsw_join args x w,
        (if (if args_pos args then not (unbox edl_is_empty_v x)
              else unbox edl_is_empty_v x)
          then ax else ag_init p (args_n args))));;

let rec udsx_join
  args x xa2 = match args, x, xa2 with
    args, x, UDSX_gen d -> UDSX_gen (de_ggc_join_msaux args x d)
    | args, x, UDSX_win w -> UDSX_win (de_gsw_join args x w)
    | args, x, UDSX_wagg (p, a) -> UDSX_wagg (p, usa_join args p x a);;

let rec uedsx_eval_since
  args rs (xs, (ys, (ts, skew))) aux =
    (match mbuf_t_cases ys
      with (None, _) ->
        (match mbuf_t_cases xs
          with (None, _) ->
            (rev rs, ((mbuf_t_empty, (mbuf_t_empty, (ts, skew))), aux))
          | (Some x, xsa) ->
            (match mbuf_t_cases ts
              with (None, _) ->
                (rev rs,
                  ((mbuf_t_Cons x xsa, (mbuf_t_empty, (mbuf_t_empty, skew))),
                    aux))
              | (Some t, tsa) ->
                (if skew || memL (args_ivl args) zero_nata
                  then (rev rs,
                         ((mbuf_t_Cons x xsa,
                            (mbuf_t_empty, (mbuf_t_Cons t tsa, skew))),
                           aux))
                  else (let auxa = udsx_join args x (udsx_add_new_ts args t aux)
                          in
                         (rev (udsx_result args auxa :: rs),
                           ((xsa, (mbuf_t_empty, (tsa, true))), auxa))))))
      | (Some y, ysa) ->
        (if skew
          then uedsx_eval_since args rs (xs, (ysa, (ts, false)))
                 (udsx_add_new_table args y aux)
          else (match mbuf_t_cases xs
                 with (None, _) ->
                   (rev rs,
                     ((mbuf_t_empty, (mbuf_t_Cons y ysa, (ts, skew))), aux))
                 | (Some x1, xs1) ->
                   (match mbuf_t_cases ts
                     with (None, ts1) ->
                       (rev rs,
                         ((mbuf_t_Cons x1 xs1,
                            (mbuf_t_Cons y ysa, (ts1, skew))),
                           aux))
                     | (Some t1, ts1) ->
                       (let aux1 =
                          udsx_add_new_table args y
                            (udsx_join args x1 (udsx_add_new_ts args t1 aux))
                          in
                         uedsx_eval_since args (udsx_result args aux1 :: rs)
                           (xs1, (ysa, (ts1, false))) aux1)))));;

let rec result_mmtaux
  args (mt, (idx_next,
              (idx_mid,
                (idx_oldest,
                  (maskL,
                    (maskR,
                      (data_prev,
                        (data_in,
                          (tuple_in_once,
                            (tuple_in_once_keys,
                              (tuple_since_hist,
                                (hist_sat, since_sat))))))))))))
    = (if is_emptya data_in
        then (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata),
               ed_insert (replicate (args_n args) None) ed_bot)
        else (args_R args,
               ed_union (ed_union tuple_in_once_keys hist_sat) since_sat));;

let rec uebuf2t_take
  f z (xs, ys) t0 ts =
    (match mbuf_t_cases ts with (None, tsa) -> (z, ((xs, ys), (t0, tsa)))
      | (Some t, tsa) ->
        (match mbuf_t_cases xs
          with (None, xsa) -> (z, ((xsa, ys), (t, mbuf_t_Cons t tsa)))
          | (Some x, xsa) ->
            (match mbuf_t_cases ys
              with (None, ysa) ->
                (z, ((mbuf_t_Cons x xsa, ysa), (t, mbuf_t_Cons t tsa)))
              | (Some y, ysa) ->
                uebuf2t_take f (f x y t z) (xsa, ysa) t tsa)));;

let rec uuw_extend
  args ts0 win rest bend cc =
    (if not bend then (win, (rest, (bend, cc)))
      else (match safe_hd rest with (None, resta) -> (win, (resta, (bend, cc)))
             | (Some e, resta) ->
               (if memR (args_ivl args) (minus_nata (fst e) ts0)
                 then uuw_extend args ts0 (append_queue e win) (tl_queue resta)
                        (snd (snd e)) (de_gcnt_add (fst (snd e)) cc)
                 else (win, (resta, (bend, cc))))));;

let rec uuw_step
  args ts0 aux =
    (let (nts, (win, (rest, (len, (bend, (cc, dn)))))) = aux in
     let (wina, (resta, (benda, cca))) = uuw_extend args ts0 win rest bend cc in
      (match safe_hd wina
        with (None, winb) ->
          (tl_queue nts,
            (winb,
              (resta,
                (minus_nata len one_nata, (benda, (cca, edl_bot :: dn))))))
        | (Some e, winb) ->
          (let winc = tl_queue winb in
           let ccaa = de_gcnt_del (fst (snd e)) cca in
           let bendb = (if is_emptya winc then true else benda) in
            (tl_queue nts,
              (winc,
                (resta,
                  (minus_nata len one_nata,
                    (bendb, (ccaa, snd cca :: dn)))))))));;

let rec uuw_shift
  args nt aux =
    (let (nts, (win, (rest, (len, (bend, (cc, dn)))))) = aux in
      (match safe_hd nts
        with (None, ntsa) -> (ntsa, (win, (rest, (len, (bend, (cc, dn))))))
        | (Some ts0, ntsa) ->
          (if memR (args_ivl args) (minus_nata nt ts0) ||
                equal_nata len zero_nata
            then (ntsa, (win, (rest, (len, (bend, (cc, dn))))))
            else uuw_shift args nt
                   (uuw_step args ts0
                     (ntsa, (win, (rest, (len, (bend, (cc, dn))))))))));;

let rec uuw_add_new
  args rel1 rel2 nt aux =
    (let (nts, (win, (rest, (len, (bend, (cc, dn)))))) = uuw_shift args nt aux
       in
     let b =
       (if args_pos args then not (unbox edl_is_empty_v rel1)
         else unbox edl_is_empty_v rel1)
       in
      (append_queue nt nts,
        (win, (append_queue (nt, (rel2, b)) rest,
                (plus_nata len one_nata, (bend, (cc, dn)))))));;

let rec udux_add_new
  args msk rel1 rel2 nt x5 = match args, msk, rel1, rel2, nt, x5 with
    args, msk, rel1, rel2, nt, UDUX_gen d ->
      UDUX_gen (de_gadd_new_dq args msk rel1 rel2 nt d)
    | args, msk, rel1, rel2, nt, UDUX_win w ->
        UDUX_win (uuw_add_new args rel1 rel2 nt w);;

let rec de_gands_pos
  x0 t us = match x0, t, us with [], t, us -> t
    | p :: ps, t, [] -> t
    | p :: ps, t, u :: us -> de_gands_pos ps (de_gbin_join p t true u) us;;

let rec de_gands_neg
  x0 t us = match x0, t, us with [], t, us -> t
    | p :: ps, t, [] -> t
    | p :: ps, t, u :: us -> de_gands_neg ps (de_gbin_join p t false u) us;;

let rec de_gmulti_join
  ps ns us =
    (match us with [] -> edl_bot
      | t :: r ->
        de_gands_neg ns (de_gands_pos ps t (take (size_lista ps) r))
          (drop (size_lista ps) r));;

let rec ueprev_next
  i xs ts =
    (match mbuf_t_cases xs with (None, _) -> ([], (mbuf_t_empty, ts))
      | (Some x, xsa) ->
        (match mbuf_t_cases ts
          with (None, _) -> ([], (mbuf_t_Cons x xsa, mbuf_t_empty))
          | (Some t, tsa) ->
            (match mbuf_t_cases tsa
              with (None, _) ->
                ([], (mbuf_t_Cons x xsa, mbuf_t_Cons t mbuf_t_empty))
              | (Some ta, tsb) ->
                (let (ys, a) = ueprev_next i xsa (mbuf_t_Cons ta tsb) in
                  ((if memL i (minus_nata ta t) && memR i (minus_nata ta t)
                     then x else edl_bot) ::
                     ys,
                    a)))));;

let rec uebufn_take
  f z buf =
    (if null buf || list_ex mbuf_t_is_empty buf then (z, buf)
      else uebufn_take f (f (mapa (comp (comp the fst) mbuf_t_cases) buf) z)
             (mapa (comp snd mbuf_t_cases) buf));;

let rec uebuf2S_add
  xsa ysa tsa (xs, (ys, (ts, skew))) =
    (mbuf_t_append xs xsa,
      (mbuf_t_append ys ysa, (mbuf_t_append ts tsa, skew)));;

let rec uebufn_add
  xsa xs = mapa (fun (a, b) -> mbuf_t_append a b) (zip xs xsa);;

let rec uuw_eval
  args nt aux =
    (let (nts, (win, (rest, (len, (bend, (cc, dn)))))) = uuw_shift args nt aux
       in
      (rev dn, (nts, (win, (rest, (len, (bend, (cc, []))))))));;

let rec udux_eval
  args nt x2 = match args, nt, x2 with
    args, nt, UDUX_gen d ->
      (let (zs, da) = de_geval_dq args nt d in (zs, UDUX_gen da))
    | args, nt, UDUX_win w ->
        (let (zs, wa) = uuw_eval args nt w in (zs, UDUX_win wa));;

let rec mebuf2T_take
  f z (xs, ys) ts =
    (match mbuf_t_cases ts with (None, tsa) -> (z, ((xs, ys), tsa))
      | (Some t, tsa) ->
        (match mbuf_t_cases xs
          with (None, xsa) -> (z, ((xsa, ys), mbuf_t_Cons t tsa))
          | (Some x, xsa) ->
            (match mbuf_t_cases ys
              with (None, ysa) ->
                (z, ((mbuf_t_Cons x xsa, ysa), mbuf_t_Cons t tsa))
              | (Some y, ysa) -> mebuf2T_take f (f x y t z) (xsa, ysa) tsa)));;

let rec reopt_table (_A1, _A2)
  x = image ((ceq_list _A1), (ccompare_list _A2))
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
          set_impl_list)
        reopt x;;

let rec udeval
  j ts db x3 = match j, ts, db, x3 with j, ts, db, UDFail -> ([], UDFail)
    | j, ts, db, UDRel rel -> (replicate (size_lista ts) rel, UDRel rel)
    | j, ts, db, UDPredS (e, ar) ->
        ((match
           lookupa
             ((ccompare_prod ccompare_string8 ccompare_nat),
               (equal_prod equal_string8 equal_nat))
             db (e, ar)
           with None -> replicate (size_lista ts) edl_bot | Some xs -> xs),
          UDPredS (e, ar))
    | j, ts, db, UDPredM (e, ar, tms, cs) ->
        ((match
           lookupa
             ((ccompare_prod ccompare_string8 ccompare_nat),
               (equal_prod equal_string8 equal_nat))
             db (e, ar)
           with None -> replicate (size_lista ts) edl_bot
           | Some a -> mapa (umatch_table tms cs) a),
          UDPredM (e, ar, tms, cs))
    | j, ts, db, UDAndRel (phi, conf) ->
        (let (xs, phia) = udeval j ts db phi in
          (mapa (edl_filter (ueval_constraint conf)) xs, UDAndRel (phia, conf)))
    | j, ts, db, UDNeg phi ->
        (let (xs, phia) = udeval j ts db phi in
          (mapa (fun r ->
                  (if unbox edl_set_eq_v r edl_bot then edl_insert [] edl_bot
                    else edl_bot))
             xs,
            UDNeg phia))
    | j, ts, db, UDExists (phi, drop0) ->
        (let (xs, phia) = udeval j ts db phi in
          ((if drop0 then mapa (edl_image tla) xs else xs),
            UDExists (phia, drop0)))
    | j, ts, db, UDAgg (g0, omega, f, k, pos, phi) ->
        (let (xs, phia) = udeval j ts db phi in
          (mapa (uagg g0 omega f k pos) xs, UDAgg (g0, omega, f, k, pos, phia)))
    | j, ts, db, UDOr (phi, psi, buf) ->
        (let (xs, phia) = udeval j ts db phi in
         let (ys, psia) = udeval j ts db psi in
         let (zs, bufa) =
           mebuf2_take
             (sup_seta
               ((ceq_list ceq_event_data), (ccompare_list ccompare_event_data)))
             (mebuf2_add xs ys buf)
           in
          (zs, UDOr (phia, psia, bufa)))
    | j, ts, db, UDAnd (pl, phi, pos, psi, buf) ->
        (let (xs, phia) = udeval j ts db phi in
         let (ys, psia) = udeval j ts db psi in
         let (zs, bufa) =
           mebuf2_take (fun r1 -> de_gbin_join pl r1 pos) (mebuf2_add xs ys buf)
           in
          (zs, UDAnd (pl, phia, pos, psia, bufa)))
    | j, ts, db, UDPrev (i, phi, first, buf, nts) ->
        (let (xs, phia) = udeval j ts db phi in
          (if first && null ts
            then ([], UDPrev
                        (i, phia, true, mbuf_t_append buf xs,
                          mbuf_t_append nts ts))
            else (let (zs, (bufa, ntsa)) =
                    ueprev_next i (mbuf_t_append buf xs) (mbuf_t_append nts ts)
                    in
                   ((if first then edl_bot :: zs else zs),
                     UDPrev (i, phia, false, bufa, ntsa)))))
    | j, ts, db, UDNext (i, phi, first, nts) ->
        (let (xs, phia) = udeval j ts db phi in
         let (xsa, firsta) =
           (match (xs, first) with ([], b) -> ([], b)
             | (_ :: xsa, true) -> (xsa, false)
             | (x :: xsa, false) -> (x :: xsa, false))
           in
         let (zs, (_, ntsa)) =
           ueprev_next i (mbuf_t_append mbuf_t_empty xsa) (mbuf_t_append nts ts)
           in
          (zs, UDNext (i, phia, firsta, ntsa)))
    | j, ts, db, UDAnds (ps, ns, ld, dbuf) ->
        (let r = mapa (udeval j ts db) ld in
         let (zs, dbufa) =
           uebufn_take
             (fun asa zs -> mbuf_t_append zs [de_gmulti_join ps ns asa])
             mbuf_t_empty (uebufn_add (mapa fst r) dbuf)
           in
          (rep_mbuf_t zs, UDAnds (ps, ns, mapa snd r, dbufa)))
    | j, ts, db, UDSince (dags, phi, psi, buf, aux) ->
        (let (xs, phia) = udeval j ts db phi in
         let (ys, psia) = udeval j ts db psi in
         let (zs, (bufa, auxa)) =
           uedsx_eval_since dags [] (uebuf2S_add xs ys ts buf) aux in
          (zs, UDSince (dags, phia, psia, bufa, auxa)))
    | j, ts, db, UDUntil (dags, msk, phi, psi, buf, nts, t, aux) ->
        (let (xs, phia) = udeval j ts db phi in
         let (ys, psia) = udeval j ts db psi in
         let (auxa, (bufa, (nt, ntsa))) =
           uebuf2t_take (udux_add_new dags msk) aux (mebuf2_add xs ys buf) t
             (mbuf_t_append nts ts)
           in
         let (zs, auxb) = udux_eval dags nt auxa in
          (zs, UDUntil (dags, msk, phia, psia, bufa, ntsa, nt, auxb)))
    | j, ts, db, UDAndAssign (p, t, phi) ->
        (let (xs, phia) = udeval j ts db phi in
          (mapa (uassign p t) xs, UDAndAssign (p, t, phia)))
    | j, ts, db, UDTP (mt, i) ->
        (mapa (fun x -> umtrm mt (EInt (integer_of_nat x))) (upt i j),
          UDTP (mt, j))
    | j, ts, db, UDTS mt ->
        (mapa (fun x -> umtrm mt (EInt (integer_of_nat x))) ts, UDTS mt)
    | j, ts, db, UDLet (p, m, phi, psi) ->
        (let (xs, phia) = udeval j ts db phi in
         let (ys, psia) =
           udeval j ts
             (updateb
               ((ccompare_prod ccompare_string8 ccompare_nat),
                 (equal_prod equal_string8 equal_nat))
               (p, m) xs db)
             psi
           in
          (ys, UDLet (p, m, phia, psia)))
    | j, ts, db, UDFrz (p, m, phi, psi, jfrz, jpsi0, jphi, alpha_s) ->
        (let (xs, phia) = udeval j ts db phi in
         let db0 =
           updateb
             ((ccompare_prod ccompare_string8 ccompare_nat),
               (equal_prod equal_string8 equal_nat))
             (p, m) [] db
           in
         let (zs0, psia) = udeval j ts db0 psi in
         let zs0_out = drop (minus_nata jfrz jpsi0) zs0 in
         let jpsi0a = plus_nata jpsi0 (size_lista zs0) in
         let alpha_sa =
           drop (plus_nata (minus_nata jfrz jphi) (size_lista zs0_out))
             (alpha_s @ xs)
           in
         let (ys, alpha_sb) =
           freeze_meval0
             (fun alpha ->
               udeval j []
                 (updateb
                   ((ccompare_prod ccompare_string8 ccompare_nat),
                     (equal_prod equal_string8 equal_nat))
                   (p, m) (replicate j alpha)
                   (map_values (ccompare_prod ccompare_string8 ccompare_nat)
                     (fun _ _ -> []) db))
                 psia)
             (minus_nata jfrz jpsi0a) alpha_sa
           in
         let jphia = plus_nata jphi (size_lista xs) in
         let jfrza =
           plus_nata (plus_nata jfrz (size_lista zs0_out)) (size_lista ys) in
          (zs0_out @ ys,
            UDFrz (p, m, phia, psia, jfrza, jpsi0a, jphia, alpha_sb)))
    | j, ts, db, UDLetPast (p, m, phi, psi, i, buf) ->
        (let (xs, (ia, (bufa, phia))) =
           letpast_meval0
             ((ccompare_prod ccompare_string8 ccompare_nat),
               (equal_prod equal_string8 equal_nat))
             size_udformula (udeval j) j i [] (list_of_option buf) (p, m) ts db
             phi
           in
         let (ys, psia) =
           udeval j ts
             (updateb
               ((ccompare_prod ccompare_string8 ccompare_nat),
                 (equal_prod equal_string8 equal_nat))
               (p, m) xs db)
             psi
           in
          (ys, UDLetPast (p, m, phia, psia, ia, bufa)))
    | j, ts, db, UDTrigger (dags, pl, phi, psi, dbuf, nts, daux) ->
        (let (xs, phia) = udeval j ts db phi in
         let (ys, psia) = udeval j ts db psi in
         let (a, b) =
           mebuf2T_take
             (fun r1 r2 t (zs, ax) ->
               (let axa = ed_update_mmtaux dags t r1 r2 ax in
                let (_, z) = result_mmtaux dags axa in
                 (zs @ [de_deopt_table z], axa)))
             ([], daux)
             (mebuf2_add
               (mapa (comp (dembedp (ceq_event_data, ccompare_event_data) pl)
                       (reopt_table (ceq_event_data, ccompare_event_data)))
                 xs)
               (mapa (reopt_table (ceq_event_data, ccompare_event_data)) ys)
               dbuf)
             (mbuf_t_append nts ts)
           in
          (let (zs, dauxa) = a in
            (fun (dbufa, ntsa) ->
              (zs, UDTrigger (dags, pl, phia, psia, dbufa, ntsa, dauxa))))
            b);;

let rec udof_m n cs (Rep_meformula e) = udof n cs e;;

let rec mstate_i (Mestate (i, j, m, n, t, zeta)) = i;;

let rec mstate_j (Mestate (i, j, m, n, t, zeta)) = j;;

let rec mstate_m (Mestate (i, j, m, n, t, zeta)) = m;;

let rec mstate_t (Mestate (i, j, m, n, t, zeta)) = linearize t;;

let rec mmonitorable_exec
  = function Eq (t1, t2) -> is_simple_eq t1 t2
    | Pred (e, ts) -> list_all (fun t -> is_Var t || is_Const t) ts
    | Let (p, phi, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
          (atLeastLessThan
            (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
            zero_nata (nfv phi))
          (fvi zero_nata phi) &&
          (mmonitorable_exec phi && mmonitorable_exec psi)
    | Frz (p, phi, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
          (atLeastLessThan
            (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
            zero_nata (nfv phi))
          (fvi zero_nata phi) &&
          (mmonitorable_exec phi && mmonitorable_exec psi)
    | LetPast (p, phi, psi) ->
        less_eq_rec_safety (safe_letpast (p, nfv phi) phi) PastRec &&
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
             (atLeastLessThan
               (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
               zero_nata (nfv phi))
             (fvi zero_nata phi) &&
            (mmonitorable_exec phi && mmonitorable_exec psi))
    | Neg phi ->
        is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
          (fvi zero_nata phi) &&
          mmonitorable_exec phi
    | Or (phi, psi) ->
        set_eq (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          (mmonitorable_exec phi && mmonitorable_exec psi)
    | And (phi, psi) ->
        mmonitorable_exec phi &&
          (safe_assignment (fvi zero_nata phi) psi ||
            (mmonitorable_exec psi ||
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata psi)
                (fvi zero_nata phi) &&
                (is_constraint psi ||
                  (match psi with Pred (_, _) -> false | Let (_, _, _) -> false
                    | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                    | Eq (_, _) -> false | Less (_, _) -> false
                    | LessEq (_, _) -> false | Neg a -> mmonitorable_exec a
                    | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                    | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                    | Prev (_, _) -> false | Next (_, _) -> false
                    | Since (_, _, _) -> false | Until (_, _, _) -> false
                    | Trigger (a, b, c) ->
                      safe_dual true mmonitorable_exec a b c
                    | Release (phia, i, psia) ->
                      bounded i &&
                        (not (memL i zero_nata && memR i zero_nata) &&
                          (mmonitorable_exec phia &&
                            (mmonitorable_exec psia &&
                              (set_eq (cenum_nat, ceq_nat, ccompare_nat)
                                 (fvi zero_nata phia) (fvi zero_nata psia) &&
                                mmonitorable_exec
                                  (and_release_safe_bounded phi phia i psia)))))
                    | MatchF (_, _) -> false | MatchP (_, _) -> false
                    | TP _ -> false | TS _ -> false))))
    | Ands l ->
        (let (pos, neg) = partition mmonitorable_exec l in
          not (null pos) &&
            (list_all mmonitorable_exec (mapa remove_neg neg) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (mapa (fvi zero_nata) neg)))
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (mapa (fvi zero_nata) pos)))))
    | Exists (t, phi) ->
        member (ceq_nat, ccompare_nat) zero_nata (fvi zero_nata phi) &&
          mmonitorable_exec phi
    | Agg (y, omega, tys, f, phi) ->
        mmonitorable_exec phi &&
          (not (member (ceq_nat, ccompare_nat) (plus_nata y (size_lista tys))
                 (fvi zero_nata phi)) &&
            (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
               (atLeastLessThan
                 (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
                 zero_nata (size_lista tys))
               (fvi zero_nata phi) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                (fvi_trm zero_nata f) (fvi zero_nata phi)))
    | Prev (i, phi) -> mmonitorable_exec phi
    | Next (i, phi) -> mmonitorable_exec phi
    | Since (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          ((mmonitorable_exec phi ||
             (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
               | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
               | Eq (_, _) -> false | Less (_, _) -> false
               | LessEq (_, _) -> false | Neg a -> mmonitorable_exec a
               | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
               | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
               | Prev (_, _) -> false | Next (_, _) -> false
               | Since (_, _, _) -> false | Until (_, _, _) -> false
               | Trigger (_, _, _) -> false | Release (_, _, _) -> false
               | MatchF (_, _) -> false | MatchP (_, _) -> false | TP _ -> false
               | TS _ -> false)) &&
            mmonitorable_exec psi)
    | Until (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          (bounded i &&
            ((mmonitorable_exec phi ||
               (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                 | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                 | Eq (_, _) -> false | Less (_, _) -> false
                 | LessEq (_, _) -> false | Neg a -> mmonitorable_exec a
                 | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                 | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                 | Prev (_, _) -> false | Next (_, _) -> false
                 | Since (_, _, _) -> false | Until (_, _, _) -> false
                 | Trigger (_, _, _) -> false | Release (_, _, _) -> false
                 | MatchF (_, _) -> false | MatchP (_, _) -> false
                 | TP _ -> false | TS _ -> false)) &&
              mmonitorable_exec psi))
    | Trigger (phi, i, psi) -> safe_dual false mmonitorable_exec phi i psi
    | Release (phi, i, psi) ->
        memL i zero_nata && memR i zero_nata &&
          (bounded i &&
            (mmonitorable_exec psi &&
              (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                 (fvi zero_nata phi) (fvi zero_nata psi) &&
                mmonitorable_exec (release_safe_0 phi i psi))))
    | MatchP (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            mmonitorable_exec phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                  | Eq (_, _) -> false | Less (_, _) -> false
                  | LessEq (_, _) -> false | Neg a -> mmonitorable_exec a
                  | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | Trigger (_, _, _) -> false | Release (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Past Strict r
    | MatchF (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            mmonitorable_exec phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
                  | Eq (_, _) -> false | Less (_, _) -> false
                  | LessEq (_, _) -> false | Neg a -> mmonitorable_exec a
                  | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | Trigger (_, _, _) -> false | Release (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Futu Strict r &&
          bounded i
    | TP t -> is_Var t || is_Const t
    | TS t -> is_Var t || is_Const t
    | Less (v, va) -> false
    | LessEq (v, va) -> false;;

let rec minit_safe
  phi = (if mmonitorable_exec phi then minit phi else failwith "undefined");;

let rec convert_multiway
  = function Pred (p, ts) -> Pred (p, ts)
    | Eq (t, u) -> Eq (t, u)
    | Less (t, u) -> Less (t, u)
    | LessEq (t, u) -> LessEq (t, u)
    | Let (p, phi, psi) -> Let (p, convert_multiway phi, convert_multiway psi)
    | Frz (p, phi, psi) -> Frz (p, convert_multiway phi, convert_multiway psi)
    | LetPast (p, phi, psi) ->
        LetPast (p, convert_multiway phi, convert_multiway psi)
    | Neg phi -> Neg (convert_multiway phi)
    | Or (phi, psi) -> Or (convert_multiway phi, convert_multiway psi)
    | And (phi, psi) ->
        (if safe_assignment (fvi zero_nata phi) psi
          then And (convert_multiway phi, psi)
          else (if safe_formula psi
                 then Ands (get_and_list (convert_multiway phi) @
                             get_and_list (convert_multiway psi))
                 else (if is_constraint psi then And (convert_multiway phi, psi)
                        else (if (match psi with Pred (_, _) -> false
                                   | Let (_, _, _) -> false
                                   | Frz (_, _, _) -> false
                                   | LetPast (_, _, _) -> false
                                   | Eq (_, _) -> false | Less (_, _) -> false
                                   | LessEq (_, _) -> false | Neg _ -> false
                                   | Or (_, _) -> false | And (_, _) -> false
                                   | Ands _ -> false | Exists (_, _) -> false
                                   | Agg (_, _, _, _, _) -> false
                                   | Prev (_, _) -> false | Next (_, _) -> false
                                   | Since (_, _, _) -> false
                                   | Until (_, _, _) -> false
                                   | Trigger (_, _, _) -> true
                                   | Release (_, _, _) -> false
                                   | MatchF (_, _) -> false
                                   | MatchP (_, _) -> false | TP _ -> false
                                   | TS _ -> false)
                               then And (convert_multiway phi,
  convert_multiway psi)
                               else (if (match psi with Pred (_, _) -> false
  | Let (_, _, _) -> false | Frz (_, _, _) -> false | LetPast (_, _, _) -> false
  | Eq (_, _) -> false | Less (_, _) -> false | LessEq (_, _) -> false
  | Neg _ -> false | Or (_, _) -> false | And (_, _) -> false | Ands _ -> false
  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
  | Next (_, _) -> false | Since (_, _, _) -> false | Until (_, _, _) -> false
  | Trigger (_, _, _) -> false | Release (_, _, _) -> true
  | MatchF (_, _) -> false | MatchP (_, _) -> false | TP _ -> false
  | TS _ -> false)
                                      then (let Release (phia, i, psia) = psi in
     (if memL i zero_nata && memR i zero_nata
       then And (convert_multiway phi, convert_multiway psi)
       else convert_multiway (and_release_safe_bounded phi phia i psia)))
                                      else Ands
     (convert_multiway psi :: get_and_list (convert_multiway phi)))))))
    | Ands phi_s -> Ands (mapa convert_multiway phi_s)
    | Exists (t, phi) -> Exists (t, convert_multiway phi)
    | Agg (y, omega, b, f, phi) -> Agg (y, omega, b, f, convert_multiway phi)
    | Prev (i, phi) -> Prev (i, convert_multiway phi)
    | Next (i, phi) -> Next (i, convert_multiway phi)
    | Since (phi, i, psi) ->
        Since (convert_multiway phi, i, convert_multiway psi)
    | Until (phi, i, psi) ->
        Until (convert_multiway phi, i, convert_multiway psi)
    | Trigger (phi, i, psi) ->
        Trigger (convert_multiway phi, i, convert_multiway psi)
    | Release (phi, i, psi) ->
        (if memL i zero_nata && memR i zero_nata
          then convert_multiway (release_safe_0 phi i psi)
          else convert_multiway (release_safe_bounded phi i psi))
    | MatchP (i, r) -> MatchP (i, map_regex convert_multiway r)
    | MatchF (i, r) -> MatchF (i, map_regex convert_multiway r)
    | TP t -> TP t
    | TS t -> TS t;;

let rec mapping_impl_choose2
  x y = match x, y with Mapping_RBT, Mapping_RBT -> Mapping_RBT
    | Mapping_Assoc_List, Mapping_Assoc_List -> Mapping_Assoc_List
    | Mapping_Mapping, Mapping_Mapping -> Mapping_Mapping
    | x, y -> Mapping_Choose;;

let rec mapping_impl_prod _A _B
  = Phantom
      (mapping_impl_choose2 (of_phantom (mapping_impl _A))
        (of_phantom (mapping_impl _B)));;

let uempty_db : ((string * nat), ((event_data list) set list)) mapping
  = mapping_empty (ccompare_prod ccompare_string8 ccompare_nat)
      (of_phantom (mapping_impl_prod mapping_impl_string8 mapping_impl_nat));;

let rec urbt_fold x = foldb (ccompare_list ccompare_event_data) x;;

let rec udmstate_cs
  (Udmstate_ext
    (udmstate_i, udmstate_j, udmstate_m, udmstate_n, udmstate_cs, udmstate_t,
      more))
    = udmstate_cs;;

let rec udmstate_t
  (Udmstate_ext
    (udmstate_i, udmstate_j, udmstate_m, udmstate_n, udmstate_cs, udmstate_t,
      more))
    = udmstate_t;;

let rec udmstate_n
  (Udmstate_ext
    (udmstate_i, udmstate_j, udmstate_m, udmstate_n, udmstate_cs, udmstate_t,
      more))
    = udmstate_n;;

let rec udmstate_m
  (Udmstate_ext
    (udmstate_i, udmstate_j, udmstate_m, udmstate_n, udmstate_cs, udmstate_t,
      more))
    = udmstate_m;;

let rec udmstate_j
  (Udmstate_ext
    (udmstate_i, udmstate_j, udmstate_m, udmstate_n, udmstate_cs, udmstate_t,
      more))
    = udmstate_j;;

let rec udmstate_i
  (Udmstate_ext
    (udmstate_i, udmstate_j, udmstate_m, udmstate_n, udmstate_cs, udmstate_t,
      more))
    = udmstate_i;;

let rec udmstep
  tdb st =
    (let (xs, m) =
       udeval (plus_nata (udmstate_j st) one_nata) [snd tdb] (fst tdb)
         (udmstate_m st)
       in
     let (i, (tq, vs)) =
       dannotate (udmstate_i st) (mbuf_t_append (udmstate_t st) [snd tdb]) xs []
       in
      (vs, Udmstate_ext
             (i, plus_nata (udmstate_j st) one_nata, m, udmstate_n st,
               udmstate_cs st, tq, ())));;

let rec udof_state
  n cs st =
    Udmstate_ext
      (mstate_i st, mstate_j st, udof_m n cs (mstate_m st), n, cs,
        mbuf_t_append mbuf_t_empty (mstate_t st), ());;

let rec strict_sorted_by
  c x1 = match c, x1 with
    c, x :: y :: zs -> equal_order (c x y) Lt && strict_sorted_by c (y :: zs)
    | c, [] -> true
    | c, [v] -> true;;

let rec rbt_of_sorted_list _A
  xa = Mapping_RBTa
         (if strict_sorted_by (the (ccompare _A)) xa
           then rbtreeify (mapa (fun x -> (x, ())) xa)
           else rbt_comp_bulkload (the (ccompare _A))
                  (mapa (fun x -> (x, ())) xa));;

let edl_rbt_of_sorted_list_v :
  ((event_data list) list -> ((event_data list), unit) mapping_rbt) boxed
  = Box (rbt_of_sorted_list (ccompare_list ccompare_event_data));;

let rec utable_of_list xs = RBT_set (unbox edl_rbt_of_sorted_list_v xs);;

let rec udminit_safe
  phi = udof_state (nfv phi) (set_cols (fvi zero_nata phi)) (minit_safe phi);;

let rec uvdfail_nodes
  = function UDFail -> one_nata
    | UDAndRel (phi, conf) -> uvdfail_nodes phi
    | UDNeg phi -> uvdfail_nodes phi
    | UDExists (phi, b) -> uvdfail_nodes phi
    | UDAgg (g0, omega, f, k, pos, phi) -> uvdfail_nodes phi
    | UDOr (phi, psi, buf) -> plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDAnd (pl, phi, pos, psi, buf) ->
        plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDPrev (i, phi, f, buf, nts) -> uvdfail_nodes phi
    | UDNext (i, phi, f, nts) -> uvdfail_nodes phi
    | UDAnds (ps, ns, l, buf) -> sum_list monoid_add_nat (mapa uvdfail_nodes l)
    | UDSince (args, phi, psi, buf, aux) ->
        plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDUntil (args, msk, phi, psi, buf, nts, t, aux) ->
        plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDAndAssign (p, t, phi) -> uvdfail_nodes phi
    | UDLet (p, m, phi, psi) ->
        plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDFrz (p, m, phi, psi, jfrz, jpsi0, jphi, alpha_s) ->
        plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDLetPast (p, m, phi, psi, i, buf) ->
        plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDTrigger (dags, pl, phi, psi, dbuf, nts, daux) ->
        plus_nata (uvdfail_nodes phi) (uvdfail_nodes psi)
    | UDRel v -> zero_nata
    | UDPredS (v, va) -> zero_nata
    | UDPredM (v, va, vb, vc) -> zero_nata
    | UDTP (v, va) -> zero_nata
    | UDTS v -> zero_nata;;

let rec mapping_rbt_insertwk _A
  xc xd xe xf =
    Mapping_RBTa
      (rbt_comp_insert_with_key (the (ccompare _A)) xc xd xe (impl_ofa _A xf));;

let rec update_mapping_with _A
  f k v (RBT_Mapping t) =
    (match ccompare _A
      with None ->
        failwith "update_mapping_with RBT_Mapping: ccompare = None"
          (fun _ -> update_mapping_with _A f k v (RBT_Mapping t))
      | Some _ -> RBT_Mapping (mapping_rbt_insertwk _A f k v t));;

let rec uinsert_table_into_db
  p x db =
    update_mapping_with (ccompare_prod ccompare_string8 ccompare_nat)
      (fun _ tbl _ -> mapa (edl_union x) tbl) p [x] db;;

end;; (*struct Monitor*)
