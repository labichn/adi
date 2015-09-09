(* Composable ADI. No dependencies. Compile with 4.02.2+:
 * > ocamlc cadi.ml
 * > ./a.out
 *)

(* monomorphic map, to test external type dependencies *)
module type MapS =
sig
  type t type key type value
  val empty : t
  val add : key -> value -> t -> t
  val find : key -> t -> value
end
module MMap(K : Map.OrderedType)(V : Map.OrderedType) = struct
  module M = Map.Make(K)
  type key   = K.t
  type value = V.t
  type t = value M.t
  let empty : t = M.empty
  let is_empty : t -> bool = M.is_empty
  let mem : key -> t -> bool = M.mem
  let add : key -> value -> t -> t = M.add
  let find : key -> t -> value = M.find
  let to_list = M.bindings
  let of_list : (K.t * V.t) list -> t =
    List.fold_left (fun a (k, v) -> add k v a) empty
end

(* base monads *)
module type M =
sig
  type 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val run : 'a t -> 'a
end

module type MF =
sig
  include M
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val foldM : ('b -> 'a -> 'b t) -> 'b -> 'a list -> 'b t
end

module MakeM(M : M) : MF with type 'a t = 'a M.t =
struct
  include M
  let (>>=) = bind
  let rec foldM =
    fun f b -> function
    |  []   -> return b
    | x::xs -> f b x >>= fun b' -> foldM f b' xs
end

module Id =
  MakeM(struct
    type 'a t = 'a
    let return a = a
    let bind m k = k m
    let run a = a
  end)

module Rd(R : sig type t val empty : t end) =
struct
  include MakeM(struct
    type 'a t = R.t -> 'a
    let return a _ = a
    let bind m k e = (k (m e)) e
    let ask e = e
    let run m = m R.empty
  end)
  let ask e = e
  let local f m e = m (f e)
end

(* Bottoms for polymorphic variants. I wouldn't need this if it were
 * possible to specify that some type t is a polymorphic variant
 * (but all tags are unknown), like `type t = private [>]`, but
 * that's not allowed. There was some work in this vein [0], but
 * there was some gap between the implementation and the theory that
 * did not get resolved.
 *
 * [0] (warning: French)
 * http://www.math.nagoya-u.ac.jp/~garrigue/papers/bardou-sep2006.pdf
 *)
module Interp =
struct
  type bot_exp   = [ `Bot ]
  type bot_value = [ `Bot ]
end

(* semantic transformers *)

module Unit =
struct

  (* Types required in any implementing language. Gets a bit
   * trickier when the types are recursive (see Arith, Abstraction).
   *)
  module T =
  struct
    type   exp = [ `Unit ]
    type value = [ `Unit ]
  end

  module Eval
    (* `Top` contains the types of our end-result: the language we're
     * building with these pieces.
     *)
    (Top  : 
     sig
       include MF      
       type   exp = private [> T.exp]
                    (* any type that includes T.exp *)
       type value = private [> T.value]
                    (* any type that includes T.value *)
       type   ops = private < eval : exp -> value t ; .. >
                    (* any polymorphic record (*cough* object *cough*)
                     * that contains `eval`. Imagine changing all of
                     * Haskell's big arrows (=>) to small arrows (->),
                     * and making each type class anonymous. This is
                     * basically what's happening here.
                     *)
     end)
    (* `Down` is the next layer down in the composition. Whenever we
     * fail to match some input in our `eval`, we pass off to
     * `Down`'s `eval`.
     *)
    (Down :
     sig
       include module type of Top
       val eval : ops -> exp -> value t
       (* The generator for the next level's eval. We fix it with
        * `tops` in this level's generator to use it.
        *)
     end) =
  struct
    include Down
    let eval tops =
      let eval = Down.eval tops in
      function
      | `Unit -> return `Unit
      |  exp  -> eval exp
  end

end

module Arith =
struct

  module T =
  struct
    (* Passing some number of types in an anonymous object type
     * is a good trick to use a single type parameter while
     * parameterizing over an arbitrary number of types. This
     * lets us easily reuse this `exp` type, regardless of the
     * rest of the types involved in the `exp` and `value` types
     * of the super-language (as long as they pass down at least
     * < exp:'exp >). We extract only the types we need out of the
     * object, and ignore the rest.
     * 
     * Here, Arith requires a type for the expressions inside of
     * Add's list. They have the type of the super-language (which
     * may include more constructors than just `Int and `Add).
     *)
    type 'types exp =
      [ `Int of int
      | `Add of 'exp list
      ] constraint 'types = < exp : 'exp ; .. >
    type value =
      [ `Int of int ]
  end

  module Eval
    (Top  : 
     sig
       include MF
       type   exp = private [> < exp:exp > T.exp]
                    (* Pass the private type of the super-language
                     * `exp` to T.exp.
                     *)
       type value = private [> T.value]
       type   ops = private < eval : exp -> value t ; .. >
     end)
    (Down :
     sig
       include module type of Top
       val eval : ops -> exp -> value t
     end) =
  struct
    include Down

    (* In this `eval` we see a use of our `tops` record (Top's ops).
     * Since the list inside an `Add node contains expressions of
     * type Top.exp, we need to pass these to the top-level `eval`
     * in our composition, not to Down's eval. The components of `tops`
     * get fixed in the implementations, see below for examples.
     *)
    let eval tops =
      let eval = Down.eval tops in
      function
      | `Int  i -> return (`Int i)
      | `Add es ->
        foldM
          (fun a e ->
            tops#eval e >>= (* recursion to the top-level *)
            fun v -> match a, v with
            | `Int i, `Int j -> return (`Int (i+j))
            | _              -> failwith "Type error in Arith.Eval.eval")
          (`Int 0)
          es
      |  exp    -> eval exp (* recursion down the composition *)
  end
end

(* This is a (simple) example of modifying semantics. If you mix this
 * in as an outer composition with Arith (or any language that contains
 * an `Int of int `exp` constructor), each (`Int i) will be interpreted
 * as (`Int -i). You can do just about any modification this way,
 * including abstract interpretation.
 *)
module NegateInt =
struct

  module T =
  struct
    type   exp = [ `Int of int ]
    type value = [ `Int of int ]
  end

  module Eval
    (Top  : 
      sig
        include MF
        type   exp = private [> T.exp]
        type value = private [> T.value]
        type   ops = private < eval : exp -> value t ; .. >
      end)
    (Down :
      sig
        include module type of Top
        val eval : ops -> exp -> value t
      end) =
  struct
    include Down
    let run a = Down.run a
    let eval tops : exp -> value t =
      let eval = Down.eval tops in
      function
      | `Int i -> return (`Int (0-i))
      |  exp   -> eval exp
  end

end

module Variables =
struct

  module T =
  struct
    type exp = [ `Var of string ]
    type value = Interp.bot_value
    (* No requirements on the type of value, but we can't specify an
     * empty polymorphic variant, so we drop in some bottom.
     *)
  end

  module Eval
    (Top  : 
      sig
        include MF
        type   env
        type   exp = private [> T.exp]
        type value = private [> T.value]
        type   ops = private
          < eval : exp -> value t
          ;  ask : env t
          ; .. >
        (* Variables requires the `tops` we pass down to expose the
         * `ask` effect. This could be required in the module type as
         * well, but it'd have to have the type `unit -> env t` since
         * it'd be defined inside a recursive module. We get hit on
         * dynamic dispatch (since OCaml's objects methods are always
         * DD), but it's prettier.
         * 
         * I've yet to try extending the top of the underlying monad
         * itself with these extensions (Top.t <> Down.t), and don't
         * know if it's possible (or desirable). This would be the
         * other justification for putting `ask` inside of `ops`.
         *)
      end)
    (R    : MapS with type     t = Top.env
                  and type   key = string
                  and type value = Top.value)
    (Down :
      sig (* Can't use `module type of Top` since `env` is abstract
           * inside it. There should be a way around this. *)
        include MF with type 'a t = 'a Top.t
        type env = Top.env type exp = Top.exp
        type ops = Top.ops type value = Top.value
        val eval : ops -> exp -> value t
      end) =
  struct
    include Down
    let eval tops : exp -> value t =
      let eval = Down.eval tops in
      function
      | `Var x -> tops#ask >>= fun r -> return (R.find x r)
      |  exp   -> eval exp
  end

end


module Abstraction =
struct

  module T =
  struct
    type 'types exp =
    [ `Lam of string * 'exp
    | `App of 'exp * 'exp
    ] constraint 'types = < exp : 'exp ; .. >

    (* Need both the expression and environment types threaded
     * in here.
     *)
    type 'types value =
    [ `Clos of 'exp * 'env
    ] constraint 'types = < exp : 'exp ; env : 'env ; .. >
  end

  module Eval
    (Top  : 
      sig
        include MF
        type   env
        type   exp = private [> < exp:'exp > T.exp] as 'exp
        type value = private [> < exp:exp ; env:env > T.value]
        type   ops = private
          <  eval : exp -> value t
          ; apply : value -> value -> value t
          ;   ask : env t
          ; .. >
      end)
    (R    : MapS with type     t = Top.env
                  and type   key = string
                  and type value = Top.value)
    (Down :
      sig
        include module type of Top
        val eval : ops -> exp -> value t
      end) =
  struct
    include Down
    let eval tops =
      let eval = Down.eval tops in
      function
      | `Lam  _ as e -> tops#ask >>= fun r -> return (`Clos (e, r))
      | `App (e, e') -> tops#eval e  >>= fun fv ->
                        tops#eval e' >>= fun av ->
                        tops#apply fv av
      |  e           -> eval e
        
  end

  module Apply
    (Top  : 
      sig
        include MF
        type   env
        type   exp = private [> < exp:'exp > T.exp] as 'exp
        type value = private [> < exp:exp ; env:env > T.value]
        type   ops = private
          <  eval : exp -> value t
          ; apply : value -> value -> value t
          ; local : 'a. (env -> env) -> 'a t -> 'a t
          ; .. >
      end)
    (R    : MapS with type     t = Top.env
                 and type   key = string
                 and type value = Top.value)
    (Down :
      sig
        include MF with type 'a t = 'a Top.t
        type env = Top.env type exp = Top.exp
        type ops = Top.ops type value = Top.value
        val apply : ops -> value -> value -> value t
      end) =
  struct
    include Down
    let apply (tops : ops) : value -> value -> value t =
      let apply = Down.apply tops in
      fun fv av -> match fv with
      | `Clos (`Lam (x, b), r) ->
        tops#local (fun _ -> R.add x av r) (tops#eval b)
      | _ -> apply fv av
  end

end

module UnitImpl =
struct

  (* Instantiate the language with its fixpoint and a trivial
   * base. It's on the composer to ensure that their `eval` is
   * total.
   *)
  module type L =
  sig
    include MF with type 'a t = 'a Id.t
    type   exp = Unit.T.exp
    type value = Unit.T.value
    type   ops = < eval : exp -> value t >
    val   eval : ops -> exp -> value t
    val    fix : unit -> ops
  end
  module rec L : L =
  struct
    include Unit.Eval(L)(struct
      include Id
      type   exp = Unit.T.exp
      type value = Unit.T.value
      type   ops = < eval : exp -> value t >
      let eval _ _ = failwith "Your eval is not total."
      end)

    (* We tie the knot by fixing the methods inside of `tops`.
     * 
     * I wish this could be done statically, but I don't think it
     * can. The other benefit of keeping `eval` a generator is that
     * the semantics of the final result can be extended (but the
     * expression and value spaces remain fixed).
     *)
    let fix () =
      let top_eval = ref (fun _ -> assert false) in
      let ops = object method eval = !top_eval end in
      top_eval := L.eval ops ;
      ops
  end
    
  include L

  (* ...success! And, this match is known to be exhaustive. *)
  let test () =
    let eval = (fix ())#eval in
    match run (eval `Unit) with
    | `Unit -> print_endline "woohoo!"

end


module ArithImpl =
struct

  module type L =
  sig
    include MF with type 'a t = 'a Id.t
    type   exp = < exp:exp > Arith.T.exp
    type value = Arith.T.value
    type   ops = < eval : exp -> value Id.t >
    val   eval : ops -> exp -> value Id.t
    val    fix : unit -> ops
  end
  module rec L : L =
  struct
    include Arith.Eval(L)(struct
      include Id
      type   exp = types Arith.T.exp
      and  types = < exp : exp >
      type value = Arith.T.value
      type   ops = < eval : exp -> value Id.t >
      let eval _ _ = failwith "Your eval is not total."
    end)
    let fix () =
      let top_eval = ref (fun _ -> assert false) in
      let ops = object method eval = !top_eval end in
      top_eval := L.eval ops ;
      ops
  end

  include L

  let test () =
    let eval = (fix ())#eval in
    match run (eval (`Add [ `Int 0 ; `Add [ `Int 1 ; `Int 2 ] ])) with
    | `Int i -> Printf.printf "Got an int: %i%!\n" i

end

module NegateArithImpl =
struct

  module type L =
  sig
    include MF with type 'a t = 'a Id.t
    type   exp = < exp:exp > Arith.T.exp
    type value = Arith.T.value
    type   ops = < eval : exp -> value Id.t >
    val   eval : ops -> exp -> value Id.t
    val    fix : unit -> ops
  end
  module rec L : L =
  struct
    include NegateInt.Eval(L)(ArithImpl)
    let fix () =
      let top_eval = ref (fun _ -> assert false) in
      let ops = object method eval = !top_eval end in
      top_eval := L.eval ops ;
      ops
  end

  include L

  let test () =
    let eval = (fix ())#eval in
    match run (eval (`Add [ `Int 0 ; `Int 1 ; `Int 2 ])) with
    | `Int i -> Printf.printf "Got an int: %i%!\n" i

end

module LcNegateArithImpl =
struct

  type 'types exp0 =
    [ 'types Arith.T.exp
    | 'types Abstraction.T.exp
    | Variables.T.exp
    | Interp.bot_exp
    ]

  type 'types value0 =
    [ 'types Abstraction.T.value
    | Arith.T.value
    | Interp.bot_value
    ]

  (* Since our state-space is recursive (env inside value, value
   * inside env), we need to define these as such. *)
  module Types =
  struct
    module rec Ty : (sig
      type exp = types exp0
      and value = types value0
      and types = < exp : exp ; env : R.t >
    end) = struct
      type exp = types exp0
      and value = types value0
      and types = < exp : exp ; env : R.t >
    end
    and R : (MapS with type   key = string
                   and type value = V.t) =
      MMap(String)(V)
    and V : (Map.OrderedType with type t = Ty.value) =
    struct
      type t = Ty.value
      let compare a b = Pervasives.compare a b
    end
    module All =
    struct
      type exp = Ty.exp
      type value = Ty.value
      type env = R.t
    end
  end

  module RdM = Rd(Types.R)

  module type L =
  sig
    include MF with type 'a t = 'a RdM.t
    type value = Types.All.value
    type exp = Types.All.exp
    type env = Types.All.env
    type ops =
      <  eval : exp -> value t
      ; apply : value -> value -> value t
      ;   ask : env t
      ; local : 'a. (env -> env) -> 'a t -> 'a t
      >
    val  eval : ops -> exp -> value t
    val apply : ops -> value -> value -> value t
    val   fix : unit -> ops
  end
  module rec L : L =
  struct

    module Eval =
      NegateInt.Eval(L)
        (Arith.Eval(L)
           (Abstraction.Eval(L)(Types.R)
              (Variables.Eval(L)(Types.R)
                 (struct
                   include RdM
                   include Types.All
                   type ops =
                     <  eval : exp -> value t
                     ; apply : value -> value -> value t
                     ;   ask : env t
                     ; local : 'a. (env -> env) -> 'a t -> 'a t
                     >
                     let eval _ _ = failwith "Your eval is not total."
                  end))))
        
    include Eval
    type env = Types.R.t

    module Apply =
      Abstraction.Apply(L)(Types.R)(struct
        include RdM
        include Types.All
        type ops =
          <  eval : exp -> value t
          ; apply : value -> value -> value t
          ;   ask : env t
          ; local : 'a. (env -> env) -> 'a t -> 'a t
          >
        let apply _ _ _ = failwith "Your apply is not total."
        let eval = eval
      end)
    let apply = Apply.apply

    let fix () =
      let top_eval  = ref (fun _ -> assert false) in
      let top_apply = ref (fun _ -> assert false) in
      let ops = object
        method  eval = !top_eval
        method apply = !top_apply
        method local : 'a. (L.env -> L.env) -> 'a L.t -> 'a L.t = RdM.local
        method   ask = RdM.ask
      end in
      let  eval = eval  ops in
      let apply = apply ops in
      top_eval  := eval  ;
      top_apply := apply ;
      ops
  end

  include L

  let test () =
    let ops = L.fix () in
    let eval, apply = ops#eval, ops#apply in
    let z = `App (`App (`Lam ("a", `Lam ("b", `App (`Var "a",
                                                    `Add [ `Int 0 ; `Int 42 ]))),
                        `Lam ("c", `Int ~-1)),
                  `Lam ("z", `Var "x")) in
    (match RdM.run (eval z) with
     | `Int   1 -> Printf.printf "Got the right lc val!: 1%!\n"
     | `Int   i -> Printf.printf "Got an int lc val: %i%!\n" i
     | `Clos  _ -> Printf.printf "Got a closure%!\n"
     (* need bot_value in here due to Variables *)
     | `Bot     -> assert false)

end

let _ =
  UnitImpl.test () ;
  ArithImpl.test () ;
  NegateArithImpl.test () ;
  LcNegateArithImpl.test ()
