(* DEFINE THE CAUSAL STRUCTURE *)

(* dimension of the observable data (X_i)'s *)
let dimension = 3

let graph : int list list = [
    [];
    [0];
    [0; 1]
  ]

(* validation *)
let () =
  if List.length graph != dimension then failwith "invalid dimension of graph";
  List.iteri (fun i incidence ->
      List.iter (fun j ->
          if j >= i then failwith "invalid graph")
        incidence)
    graph

(* DEFINE THE UNIVERSE *)

(* the universe is an assignment to the 'unobserved terms' in the causal structure *)

let rec all_bool_lists len =
  if len = 0 then [[]]
  else
    (List.concat_map
       (fun u -> [true :: u; false :: u])
       (all_bool_lists (len - 1)))

(* type of an assignment of the unobserved terms *)
type universe = bool list

let all_universes : universe list = all_bool_lists dimension


(* DEFINE THE META-UNIVERSE *)

(* a meta universe is a vector of truth tables defining each observable term
   in terms of its unobservable term and prior observable terms
 *)


(* reduce a list of bools (i.e. a binary number) to a native int (head = lsb) *)
let rec bool_list_collapse = function
  | [] -> 0
  | true :: rem -> 1 + 2 * (bool_list_collapse rem)
  | false :: rem -> 2 * (bool_list_collapse rem)

(* return all lists formed by taking one element each from a list of lists *)
let rec choice = function
  | [] -> [[]]  
  | head :: rem ->
      let choice_rem = choice rem in
      List.concat_map (fun x ->
        List.map (fun combination -> x :: combination) choice_rem
        ) head

(* the above is not polymorphic - for pairs we can make it poly *)
let choice_poly_pair la lb =
  List.concat_map (fun a -> 
      List.map (fun b -> (a, b)) lb
  ) la

type meta = bool list list

let all_metas : meta list =
  choice (List.map (fun parents ->
              all_bool_lists
                (1 + bool_list_collapse
                       (List.init (1 + List.length parents) (Fun.const true))))
            graph)

(* DEFINE AXIOMATIC ACTIONS *)

(* "observations" collapse truth tables against a universe of
   unobservables to obtain  concrete values for each observable
 *)

(* "interventions" overwrite particular truth tables to reflect
   replacement of a latent variable causal mechanism with a
   provided invariant causal mechanism
 *)

(* calculates the observable data X_i *)
let rec observe (u : universe) (m : meta) (idx : int) : bool =
  if idx >= dimension then failwith "invalid idx" else
    let parent_vals = List.map (observe u m) (List.nth graph idx) in
    let parents_case = bool_list_collapse ((List.nth u idx) :: parent_vals) in
    List.nth (List.nth m idx) parents_case

(* replaces one of the truth tables in meta with a constant "intervention" table *)
let intervene (idx : int) (sgn : bool) : meta -> meta =
  List.mapi (fun idx' ->
      if idx' = idx then
        (List.map (Fun.const sgn))
      else
        Fun.id)


(* DEFINE EXPERIMENTAL PROGRAMS *)

(* programs act to discriminate amongst universes and meta-universes
   by producing results that depend on their (often subtle) properties
 *)

type term =
  | Assign of bool * int
  | Intervene of bool * int
  | Measure of int

type program = term list

type result = bool list

(* DEFINE PROGRAM EVALUATION *)

let rec evaluate (u : universe) (m : meta) : program -> result = function
  | Assign (sgn, idx) :: rem ->
     if (observe u m idx) = sgn then
       evaluate u m rem
     else []

  | Intervene (sgn, idx) :: rem ->
     evaluate u (intervene idx sgn m) rem

  | Measure (idx) :: rem ->
     (observe u m idx) :: (evaluate u m rem)
  | [] -> []

(* DEFINE FREQUENTIST ANALYSIS *)

module ResultMap = Map.Make(struct
                       type t = result
                       let compare = compare
                     end)

let domain_results (domain : meta list) (p : program) =
  let domain = choice_poly_pair all_universes domain in
  let norm_count_over_domain n = n /. float_of_int (List.length domain) in
  let results = List.map (function
                    | (u, m) -> evaluate u m p) domain in
  let incr prior result = ResultMap.update result (function
                              | Some n -> Some (n +. 1.)
                              | None -> Some 1.) prior in
  ResultMap.map norm_count_over_domain (List.fold_left incr ResultMap.empty results)

let discriminate_domain (signal : meta -> bool) (p : program) =
  let pos_domain = List.filter signal all_metas in
  let neg_signal = Fun.compose not signal in
  let neg_domain = List.filter neg_signal all_metas in
  ResultMap.merge
    (fun _ pos_freq neg_freq -> match (pos_freq, neg_freq) with
                                    | Some p, Some n -> Some (p /. n, p, n)
                                    | Some p, None -> Some (max_float, p, 0.)
                                    | None, Some n -> Some (0., 0., n)
                                    | None, None -> None)

    (domain_results pos_domain p)
    (domain_results neg_domain p)

let likelihood_characteristic (signal : meta -> bool) (p : program) =
  discriminate_domain signal p
  |> ResultMap.bindings
  |> List.map snd
  |> List.sort (fun (l1, _, _) (l2, _, _) -> compare l2 l1)
  |> List.fold_left (function
         | (l_prev, pd_prev, pf_prev) :: tl ->
            fun (l, p, n) ->
            (l, pd_prev +. p, pf_prev +. n) :: (
              if l = l_prev then tl else
                (l_prev, pd_prev, pf_prev) :: tl)
         | _ -> failwith "empty init passed") [(max_float, 0., 0.)]

let pf_pd signal p =
  likelihood_characteristic signal p |> List.map (fun (_, pd, pf) -> (pf, pd))

(* GRAPH UTIL *)

let plot_scatter data =
  let gp = Gnuplot.create () in

  let output = Gnuplot.Output.create `Qt in

  let labels = Gnuplot.Labels.create ~x:"False Alarm Probability" ~y:"Detection Probability" () in

  let range = Gnuplot.Range.XY (0.0, 1.0, 0.0, 1.0) in

  let dumb = Gnuplot.Series.linespoints_xy ~title:"ignorant classifier" ~color:`Black [(0., 0.); (1., 1.)] in
  let p05 = Gnuplot.Series.linespoints_xy ~color:`Red [(0.05, 0.); (0.05, 1.)] in
  let series = dumb :: p05 ::
                 (data |> List.map (fun (title, data) ->
                              Gnuplot.Series.linespoints_xy ~title:title data)) in
  Gnuplot.plot_many ~output ~labels ~range gp series;
  
  ignore (read_line ());
  Gnuplot.close gp

(* EXAMPLES *)

let threshold = 0.4

let lookup k m =
  match ResultMap.find_opt k m with
  | Some v -> v
  | None -> 0.

(* this signal identifies meta universes in which the probability of X2 is significantly
   greater (additive threshold) given X1 than given not X1 *)
let reccomend_one_for_two_signal m : bool =
  let one_pos_results = domain_results [m] [Assign (true, 1); Measure 2] in
  let one_neg_results = domain_results [m] [Assign (false, 1); Measure 2] in
  let prob_two_given_one =
    (lookup [true] one_pos_results) /. (1. -. lookup [] one_pos_results) in
  let prob_two_given_none =
    (lookup [true] one_neg_results) /. (1. -. lookup [] one_neg_results) in
  prob_two_given_one > prob_two_given_none +. threshold

let () = [
    ("maximal", [Measure 0; Measure 1; Measure 2;
                 Intervene (true, 0); Intervene (true, 1); Measure 2;
                 Intervene (true, 1); Intervene (true, 0); Measure 2]);
    ("observe 12", [Measure 1; Measure 2]);
    ("intervene 0", [Intervene (true, 0); Measure 2]);
    ("intervene 1", [Intervene (true, 1); Measure 2]);
    ("intervene 01", [Intervene (true, 1); Intervene (true, 0); Measure 2])
  ] |> List.map (fun (title, prog) -> (title, pf_pd reccomend_one_for_two_signal prog))
         |> plot_scatter

(* to run:
   dune exec ./operationalize.exe
 *)
