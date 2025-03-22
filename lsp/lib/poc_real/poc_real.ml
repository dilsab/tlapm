let h () = ()

(* let sq_to_str sq =
  let buf = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buf in
  let obll = Tlapm_lib.Proof.T.obligation (_, _, _, _) in
  Tlapm_lib.Proof.Fmt.pp_print_sequent fmt obll;
  Format.pp_print_flush fmt ();
  Buffer.contents buf *)

let%test_unit "proof explanationn" =
  let filename = "poc_real.tla" in
  let content =
    String.concat "\n"
      [
        "---- MODULE poc_real ----";
        (* "EXTENDS FiniteSetTheorems"; *)
        (* "THEOREM TRUE";
        "    <1>1. TRUE OBVIOUS";
        "    <1>2. FALSE OBVIOUS";
        "    <1>q. QED BY <1>1, <1>2"; *)
        (* "THEOREM TRUE";
        "    <1>q. QED BY TRUE";
        "THEOREM TRUE BY TRUE"; *)
        "THEOREM ProveNegationByContradiction ==";
        "  ASSUME NEW P PROVE ~P";
        "PROOF";
        "  <1>c. ASSUME P PROVE FALSE OMITTED";
        "  <1>q. QED BY <1>c";
        "====";
      ]
  in
  let mule =
    Result.get_ok (Parser.module_of_string ~content ~filename ~loader_paths:[])
  in
  let rec t_usable_fact (fact : Tlapm_lib__.Expr.T.expr) =
    let open Tlapm_lib in
    (* List.iter (fun (_prop : Property.prop) -> ()) (Property.props_of fact); *)
    (* Property.print_all_props fact;
    Stdlib.flush_all (); *)
    let nm =
      match fact.core with
      | Expr.T.Ix n -> "Ix" ^ string_of_int n
      | Expr.T.Opaque s -> "Opaque-" ^ s
      | Expr.T.Internal i -> (
        match i with
        | TRUE -> "TRUE"
        | FALSE -> "FALSE"
        | Implies -> "Implies"
        | Equiv -> "Equiv"
        | Conj -> "Conj"
        | Disj -> "Disj"
        | Neg -> "Neg"
        | Eq -> "Eq"
        | Neq -> "Neq"
        | STRING -> "STRING"
        | BOOLEAN -> "BOOLEAN"
        | SUBSET -> "SUBSET"
        | UNION -> "UNION"
        | DOMAIN -> "DOMAIN"
        | Subseteq -> "Subseteq"
        | Mem -> "Mem"
        | Notmem -> "Notmem"
        | Setminus -> "Setminus"
        | Cap -> "Cap"
        | Cup -> "Cup"
        | Prime -> "Prime"
        | StrongPrime -> "StrongPrime"
        | Leadsto -> "Leadsto"
        | ENABLED -> "ENABLED"
        | UNCHANGED -> "UNCHANGED"
        | Cdot -> "Cdot"
        | Actplus -> "Actplus"
        | Box true -> "Box(true)"
        | Box false -> "Box(false)"
        | Diamond -> "Diamond"
        | Nat -> "Nat"
        | Int -> "Int"
        | Real -> "Real"
        | Plus -> "Plus"
        | Minus -> "Minus"
        | Uminus -> "Uminus"
        | Times -> "Times"
        | Ratio -> "Ratio"
        | Quotient -> "Quotient"
        | Remainder -> "Remainder"
        | Exp -> "Exp"
        | Infinity -> "Infinity"
        | Lteq -> "Lteq"
        | Lt -> "Lt"
        | Gteq -> "Gteq"
        | Gt -> "Gt"
        | Divides -> "Divides"
        | Range -> "Range"
        | Seq -> "Seq"
        | Len -> "Len"
        | BSeq -> "BSeq"
        | Cat -> "Cat"
        | Append -> "Append"
        | Head -> "Head"
        | Tail -> "Tail"
        | SubSeq -> "SubSeq"
        | SelectSeq -> "SelectSeq"
        | OneArg -> "OneArg"
        | Extend -> "Extend"
        | Print -> "Print"
        | PrintT -> "PrintT"
        | Assert -> "Assert"
        | JavaTime -> "JaveTime"
        | TLCGet -> "TLCGet"
        | TLCSet -> "TLCSet"
        | Permutations -> "Permutations"
        | SortSeq -> "SortSeq"
        | RandomElement -> "RandomElement"
        | Any -> "Any"
        | ToString -> "ToString"
        | Unprimable -> "Unprimable"
        | Irregular -> "Irregular"
        )
      | Expr.T.Lambda (_, _) -> "Lambda"
      | Expr.T.Sequent sq -> (
        t_sq sq;
        "Sequent"
      )
      | Expr.T.Bang (_, _) -> "Bang"
      | Expr.T.Apply (e, e_l) -> (
        t_usable_fact e;
        List.iter t_usable_fact e_l;
        "Apply"
      )
      | Expr.T.With (_, _) -> "With"
      | Expr.T.If (_, _, _) -> "If"
      | Expr.T.List (_, _) -> "List"
      | Expr.T.Let (_, _) -> "Let"
      | Expr.T.Quant (_, _, _) -> "Quant"
      | Expr.T.QuantTuply (_, _, _) -> "QuantTuply"
      | Expr.T.Tquant (_, _, _) -> "Tquant"
      | Expr.T.Choose (_, _, _) -> "Choose"
      | Expr.T.ChooseTuply (_, _, _) -> "ChooseTuply"
      | Expr.T.SetSt (_, _, _) -> "SetSt"
      | Expr.T.SetStTuply (_, _, _) -> "SetStTuply"
      | Expr.T.SetOf (_, _) -> "SetOf"
      | Expr.T.SetOfTuply (_, _) -> "SetOfTuply"
      | Expr.T.SetEnum _ -> "SetEnum"
      | Expr.T.Product _ -> "Product"
      | Expr.T.Tuple _ -> "Tuple"
      | Expr.T.Fcn (_, _) -> "Fcn"
      | Expr.T.FcnTuply (_, _) -> "FcnTuply"
      | Expr.T.FcnApp (_, _) -> "FcnApp"
      | Expr.T.Arrow (_, _) -> "Arrow"
      | Expr.T.Rect _ -> "Rect"
      | Expr.T.Record _ -> "Record"
      | Expr.T.Except (_, _) -> "Except"
      | Expr.T.Dot (_, _) -> "Dot"
      | Expr.T.Sub (_, _, _) -> "Sub"
      | Expr.T.Tsub (_, _, _) -> "Tsub"
      | Expr.T.Fair (_, _, _) -> "Fair"
      | Expr.T.Case (_, _) -> "Case"
      | Expr.T.String _ -> "String"
      | Expr.T.Num (_, _) -> "Num"
      | Expr.T.At _ -> "At"
      | Expr.T.Parens (_, _) -> "Parens"
    in
    match Property.query fact Proof.T.Props.use_location with
    | None ->
        Eio.traceln "Fact %s, %s %a" nm
          (Util.location fact)
          (Format.pp_print_option Proof.T.pp_stepno)
          (Property.query fact Proof.T.Props.step)
    | Some loc ->
        Eio.traceln "Fact %s" (Loc.string_of_locus loc)
and t_sq (sq : Tlapm_lib.Expr.T.sequent) = (
  t_usable_fact sq.active;
  List.iter t_hyp (Tlapm_lib__Deque.to_list sq.context)
  (* match Tlapm_lib__Deque.front sq.context with
  | Some v ->  t_hyp v
  | None -> () *)
)

and t_hyp (hy : Tlapm_lib.Expr.T.hyp) = (
  match hy.core with
  | Fresh (hint, _, _, hdom) -> (
    Eio.traceln "Fresh %s" hint.core;
    match hdom with
    | Unbounded -> Eio.traceln "Unbounded"
    | Bounded (expr, _) -> (
      Eio.traceln "Bounded";
      t_usable_fact expr;
    )
  )
  | FreshTuply (_, _) -> Eio.traceln "FreshTuply"
  | Flex (_) -> Eio.traceln "Flex"
  | Defn (defn, _, _, _) -> (
    match defn.core with
    | Recursive (hint, _) -> (
      (* hint * shape *)
      Eio.traceln "Defn Recursive %s" hint.core
    )
    | Operator (hint, expr)  -> (
      (* hint * expr *)
      Eio.traceln "Defn Operator %s" hint.core;
      t_usable_fact expr;
    )
    | Instance (hint, _)  -> (
      (* hint * instance *)
      Eio.traceln "Defn Instance %s" hint.core
    )
    | Bpragma (hint, _, _) -> (
      Eio.traceln "Defn Bpragma %s" hint.core
    )
  )
  | Fact (fact, _, _) -> (
    (* Eio.traceln "Fact"; *)
    t_usable_fact fact;
  )
)
  and t_step (st : Tlapm_lib.Proof.T.step) =
    match st.core with
    | Tlapm_lib.Proof.T.Assert (sq, pf) -> (
      t_proof pf;
      t_sq sq;
      )
    | Tlapm_lib.Proof.T.Hide _ -> Eio.traceln "Hide"
    | Tlapm_lib.Proof.T.Define _ -> Eio.traceln "Define"
    | Tlapm_lib.Proof.T.Suffices (_, _) -> Eio.traceln "Suffices"
    | Tlapm_lib.Proof.T.Pcase (_, _) -> Eio.traceln "Pcase"
    | Tlapm_lib.Proof.T.Pick (_, _, _) -> Eio.traceln "Pick"
    | Tlapm_lib.Proof.T.PickTuply (_, _, _) -> Eio.traceln "PickTuply"
    | Tlapm_lib.Proof.T.Use (_, _) -> Eio.traceln "Use"
    | Tlapm_lib.Proof.T.Have _ -> Eio.traceln "Have"
    | Tlapm_lib.Proof.T.Take _ -> Eio.traceln "Take"
    | Tlapm_lib.Proof.T.TakeTuply _  -> Eio.traceln "TakeTuply"
    | Tlapm_lib.Proof.T.Witness _ -> Eio.traceln "Witness"
    | Tlapm_lib.Proof.T.Forget _  -> Eio.traceln "Forget"
  and t_qed_step (qs : Tlapm_lib.Proof.T.qed_step) =
    match qs.core with Tlapm_lib.Proof.T.Qed pf -> t_proof pf
  and t_proof (pf : Tlapm_lib.Proof.T.proof) =
    match pf.core with
    | Tlapm_lib.Proof.T.Steps (sts, qed) -> (
        let open Tlapm_lib in
        List.iter t_step sts;
        t_qed_step qed;
        match Property.query qed Proof.Parser.qed_loc_prop with
        | None -> Eio.traceln "_______XXXXXXXXXX: StepsLOC - none"
        | Some qed_loc ->
            Eio.traceln "_______XXXXXXXXXX: StepsLOC, %a, %s" Proof.T.pp_stepno
              (Property.get qed Proof.T.Props.step)
              (Loc.string_of_locus qed_loc))
    | Tlapm_lib.Proof.T.By (usable, _only) ->
        List.iter t_usable_fact usable.facts
    | Tlapm_lib.Proof.T.Obvious -> Eio.traceln "Obvious"
    | Tlapm_lib.Proof.T.Omitted _ -> ()
    | Tlapm_lib.Proof.T.Error _ -> Eio.traceln "Error"
  and t_moduint (mu : Tlapm_lib.Module.T.modunit) =
    match mu.core with
    | Tlapm_lib.Module.T.Theorem (_nm, sq, _naxs, _pf, pf_orig, _summ) ->
      (
        Eio.traceln "Proving theorem:";
        t_sq sq;
        Eio.traceln "Proven by:";
        (* Eio.traceln ">>>>>>pf:";
        t_proof pf; *)
        Eio.traceln ">>>>>>pf_orig:";
        t_proof pf_orig; (* Only the orig contains the qed_loc_prop*)
      )
    | Tlapm_lib.Module.T.Constants _ | Tlapm_lib.Module.T.Recursives _
    | Tlapm_lib.Module.T.Variables _
    | Tlapm_lib.Module.T.Definition (_, _, _, _)
    | Tlapm_lib.Module.T.Axiom (_, _)
    | Tlapm_lib.Module.T.Submod _
    | Tlapm_lib.Module.T.Mutate (_, _)
    | Tlapm_lib.Module.T.Anoninst (_, _) ->
        ()
  and t_mule (m : Tlapm_lib.Module.T.mule) = List.iter t_moduint m.core.body in
  let () = t_mule mule in let _ = Eio.traceln "defdepth %d" mule.core.defdepth
    in let _ = 
    match mule.core.stage with
    | Special -> Eio.traceln "Special"
    | Parsed -> Eio.traceln "Parsed"
    | Flat -> Eio.traceln "Flat"
    | Final (_) -> Eio.traceln "Final"
    in ()
