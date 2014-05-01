(****** Project for CS-565 Programming Languages - Purdue. ******)
(** * Project: Max Flow / Min Cut *)

(* Formalize a graph network with edges labelled with their capacity. *) 
(* Prove max-flow/min-cut theorem of Graph Theory. *)

(** edgardo barsallo (ebarsall@purdue.edu) *)
(** servio palacios (spalacio@purdue.edu) *)

Lemma Admitted : forall P:Prop, P.
Proof. admit. Qed.

(* Require Export Coq.Sets.Ensembles. *)
(* Require Export Coq.Arith.EqNat. *)
(* Require Export Coq.Lists.List. *)
Require Export SfLib.


(* ###################################################### *)
(** * Graph Representation (Definitions) *)

(** **** Vertex *)
Inductive VerName : Set :=
    index : nat -> VerName.

Definition Weight := nat.

Definition Flow := nat.

Definition adjacence : Type := (VerName * Weight * Flow) % type.

Inductive vertex := 
  v_cons : VerName -> list adjacence -> vertex. 

(** **** Graph *)
(** The graph is represented as trio of the following elements: [1] list of vertices that
    conforms the graph; [2] [VerName] of the source vertex; and [3] [VerName] of the sink 
    vertex. *)
Definition graph := ((list vertex) * VerName * VerName) % type.

(** [beq_VerName]: Compare if two [VerName] are equal. Returns [true] if both 
    are equal ([vn1] and [vn2]), otherwise returns [false]. *)
Definition beq_VerName (vn1 vn2:VerName) : bool :=
 match vn1, vn2 with
   | index n1, index n2 =>
      if beq_nat n1 n2 then true else false
 end.

(** [weight_lookup]: Lookup the weight (capacity) for a [VerName] in a adjacence 
    list. 
    Returns the [Weight] if the [VerName] exists in the adjance list, otherwise 
    returns [None]. *)
Fixpoint weight_lookup (ls:list adjacence) (vn:VerName) : option Weight :=
 match ls with
   | nil => None
   | cons (pair (pair adjVn adjW) adjF) xs =>  
     if beq_VerName adjVn vn then Some adjW
     else weight_lookup xs vn
 end.

(** [flow_lookup]: Lookup the network flow for a [VerName] in a adjacence list. 
    Returns the [Weight] if the [VerName] exists in the adjance list, otherwise 
    returns [None]. *)
Fixpoint flow_lookup (ls:list adjacence) (vn:VerName) : option Flow :=
 match ls with
   | nil => None
   | cons (pair (pair adjVn adjW) adjF) xs =>  
     if beq_VerName adjVn vn then Some adjF
     else flow_lookup xs vn
 end.

(** [vertex_lookup]: Lookup for a [vertex] in a [Graph]. Returns the [vertex] 
    if the [VerName] exists in the [Graph], otherwise returns [None] *)
Fixpoint vertex_lookup_vls (vls:list vertex) (vn:VerName) : option vertex :=
  match vls with
    | nil => None
    | cons vn1 al => 
      match  vn1 with
        | (v_cons hvn vnla) => 
           if beq_VerName hvn vn 
           then Some vn1
           else vertex_lookup_vls al vn
      end
  end.

Definition vertex_lookup (grph:graph) (vn:VerName) : option vertex :=
  match grph with 
    | pair (pair vls src) snk => vertex_lookup_vls vls vn 
  end.

(** [adj_vertex_lookup]: Lookup for a [vertex] in a adjacence list. Returns a 
    [vertex] of a [Graph] if a [VerName] exists in the adjence list, otherwise 
    returns [None]. *)
Fixpoint adj_vertex_lookup (grph:graph) (ls:list adjacence) (vn:VerName) :
 option vertex :=
 match ls with
   | nil => None
   | cons adjVx xs =>  
     match adjVx with
       | pair (pair adjVn adjW) adjF =>
         if beq_VerName adjVn vn then vertex_lookup grph adjVn
         else adj_vertex_lookup grph xs vn
     end
 end.


(** [path_weight]: Compute the weight in a path, starting from a current vertex 
    [cur] hopping thru all the vertex contained in a list of VerName [l]. The 
    list of VerName [l] should be in order (of hop). *)
Fixpoint path_weight (grph:graph) (cur:vertex) (l:list VerName) :
  option nat := 
  match l with
    | nil => Some 0
    | cons vn l' => 
      match cur with
          v_cons vn' ladj =>
          match weight_lookup ladj vn with
            | None => None
            | Some n =>
              match adj_vertex_lookup grph ladj vn with
                | None => None
                | Some v' => 
                  match path_weight grph v' l' with
                    | None => None 
                    | Some m => Some (n + m)
                  end
              end
          end
      end
  end.

(** [path_flow]: Compute the net flow in a path, starting from a current vertex
    [cur] hopping thru all the vertex contained in a list of VerName [l]. The 
    list of VerName [l] should be in order (of hop).
    Similar to [path_weight]. *)
Fixpoint path_flow (grph:graph) (cur:vertex) (l:list VerName) :
  option nat := 
  match l with
    | nil => Some 0
    | cons vn l' => 
      match cur with
          v_cons vn' ladj =>
          match flow_lookup ladj vn with
            | None => None
            | Some n =>
              match adj_vertex_lookup grph ladj vn with
                | None => None
                | Some v' => 
                  match path_flow grph v' l' with
                    | None => None 
                    | Some m => Some (n + m)
                  end
              end
          end
      end
  end.

(** [edge_weight]: Compute the weight in a edge, two vertices directly connected
    which each other. *)
Definition edge_weight (grph :graph) (vn0 vn1:VerName) : option nat :=
  match vertex_lookup grph vn0 with
    | None => None
    | Some v' => path_weight grph v' (cons vn1 nil)
  end.

(** [edge_flow]: Compute the flow in a edge, two vertices directly connected
    which each other. *)
Definition edge_flow (grph :graph) (vn0 vn1:VerName) : option nat :=
  match vertex_lookup grph vn0 with
    | None => None
    | Some v' => path_flow grph v' (cons vn1 nil)
  end.

(** [ble_weight]: Compare two [weight]: [w1] and [w2] (capacity or network flow) and 
    return [true] if [w1] is less and equal than [w2], otherwise returns [false]. *)
Definition ble_weight (w1 w2: option nat) : bool :=
  match w1 with
    | None => false
    | Some n1' => 
      match w2 with
        | None => false
        | Some n2' => ble_nat n1' n2'
      end
  end.

(** [ble_weight]: Compare two [weight]: [w1] and [w2] (capacity or network flow) and 
    return [true] if [w1] and [w2] are equal, otherwise returns [false]. *)
Definition beq_weight (w1 w2: option nat) : bool :=
  match w1 with
    | None => false
    | Some n1' => 
      match w2 with
        | None => false
        | Some n2' => beq_nat n1' n2'
      end
  end.

(** [vertex_flow_out]: Compute the sum of network flow comming out a [VerName] [vn], which is
    the network flow produce by a vertex. *)
Fixpoint sum_flow_out_adjls (ls :list adjacence) : nat :=
 match ls with
   | nil => 0
   | cons (pair (pair adjVn adjW) adjF) xs =>  
     adjF + sum_flow_out_adjls xs
  end.

Fixpoint vertex_flow_out (grph :graph) (vn :VerName) : option nat :=
  match vertex_lookup grph vn with
    | None => None
    | Some v' => 
      match v' with
        | v_cons vn' al' => 
          match sum_flow_out_adjls al' with
            | 0 => None
            | n => Some n
          end
      end
  end.

(** [vertex_flow_in]: Compute the sum of network flow comming in a [VerName] [vn], which is
    the network flow consume by a vertex. *)
Fixpoint sum_flow_in_vls (vls :list vertex) (vn :VerName) : nat :=
  match vls with
    | nil => 0
    | cons v' vl' =>
      match v' with
        | v_cons vn' al' => 
           match weight_lookup al' vn with 
             | None => 0 + sum_flow_in_vls vl' vn
             | Some n' => n' + sum_flow_in_vls vl' vn
           end
       end
   end.

Fixpoint vertex_flow_in (grph :graph) (vn :VerName) : option nat :=
  match grph with 
    | pair (pair vls src) snk => 
      match sum_flow_in_vls vls vn with
        | 0 => None
        | n => Some n
      end
  end.

(** [beq_internal_vertex]: Checks if a [VerName] [vn] is an internal vertex, which means
    [vn] is not neither source vertex nor the sink vertex.
    Returns [true] if [vn] is internal, otherwise returns [false].*)
Fixpoint beq_internal_vertex (grph :graph) (vn :VerName) : bool :=
  match grph with 
    | pair (pair vls src) snk => 
      if andb (negb (beq_VerName src vn)) (negb (beq_VerName snk vn)) then true else false
  end.

Definition graph_list (grph :graph) : list vertex :=
  match grph with 
    | pair (pair vls src) snk => vls
  end.

Definition beq_vertex (v1 v2: vertex) : bool :=
  match v1 with
    | v_cons vn1 vlist1 => 
      match v2 with
        | v_cons vn2 vlist2 => beq_VerName vn1 vn2
      end 
  end.

(* ###################################################### *)
(** * Lists extended functions *)

(** [last]: Get the last element in a list of type [A]. *)
Fixpoint lastA {A:Type} (default:A) (ls:list A) : A :=
  match ls with
    | nil          => default
    | cons a nil   => a
    | cons a tail  => lastA default tail
  end.


(** [In]: Verify if an element exists in a list of type [A]. Returns a Prop.
    Adapted from Lists.v. *)
Fixpoint In {A :Type} (a:A) (l:list A) (f :A->A->bool) : bool :=
  match l with
    | nil => false
    | cons b m => orb (f a b)  (In a m f)
  end.

(** [In_Set]: Verify if all the element of a list [ls1] does not exists in 
    other list ([ls2]). Returns a Prop.
    Adapted from Lists.v. *)
Fixpoint In_Set {A :Type} (ls1 ls2 :list A) (f :A->A->bool) : bool :=
  match ls1 with
    | nil => false
    | cons b m => orb (In b ls2 f) (In_Set m ls2 f)
  end.

(** [Disjoint]: Verify if two list of type [A] are disjoint, does not any
    element in common. *)
Definition disjoint {A :Type} (ls1 ls2 :list A) (f :A->A->bool): bool :=
  orb (In_Set ls1 ls2 f) (In_Set ls2 ls1 f).

Inductive NoRep {A :Type}: list A -> Prop :=
    | NoRep_nil : NoRep nil
    | NoRep_cons : forall (x :A) (l: list A) (f :A->A->bool), 
         In x l f = false -> NoRep l -> NoRep (x::l).


(* ###################################################### *)
(** * Direct Graph: Properties, Lemmas and Theorems *)

(** Inductive property for a [path] in a Direct [Graph] with Weights in each edge. *)
Inductive graph_path (grph:graph) : VerName -> list VerName -> Weight -> Prop :=
  (* | path_empty : forall (v:VerName) v',  *)
  (*                  vertex_lookup grph v = Some v' -> *)
  (*                  (path grph v (v::nil) 0) *)
  | path_one : forall (v0 v1:VerName) (v:vertex) vls w, 
                 v0 <> v1 -> 
                 vertex_lookup grph v0 = Some (v_cons v1 vls) -> 
                 weight_lookup vls v1 = Some w -> 
                 (graph_path grph v0 (v1::nil) w)
  | path_trans : forall (v1 v2 default:VerName) (ls1 ls2 : list VerName) 
                        (n0 n1:Weight), 
                   (graph_path grph v1 ls1 n0) -> 
                   lastA default ls1 = v2 -> 
                   (graph_path grph v2 ls2 n1) -> 
                   disjoint ls1 ls2 beq_VerName = true ->  
                   (graph_path grph v1 (ls1++ls2) (n0 + n1)).


(** Inductive property to verify that a [graph] is well formed. *)
Inductive graph_well_formed : graph -> Prop :=
  | vtx_unique : forall (vn:VerName) (v:vertex) (grph:graph) (vls:list vertex) ,
                   vertex_lookup grph vn = Some v ->
                   {vls = (graph_list grph)} + {vls <> (graph_list grph)} ->
                   In v vls beq_vertex = true ->
                   NoRep vls ->
                   graph_well_formed grph
  | vtx_source : forall (vsrc:VerName) (grph:graph) w v vls,
                   vertex_lookup grph vsrc = Some v->
                   {vls = (graph_list grph)} + {vls <> (graph_list grph)} ->
                   In v vls beq_vertex = true ->
                   beq_internal_vertex grph vsrc = false ->
                   vertex_flow_in grph vsrc = Some 0 ->
                   vertex_flow_out grph vsrc = Some w ->
                   graph_well_formed grph
  | vtx_sink : forall (vsnk:VerName) (grph:graph) w v vls,
                 vertex_lookup grph vsnk = Some v->
                 {vls = (graph_list grph)} + {vls <> (graph_list grph)} ->
                 In v vls beq_vertex = true ->
                 beq_internal_vertex grph vsnk = false ->
                 vertex_flow_in grph vsnk = Some w ->
                 vertex_flow_out grph vsnk = Some 0 ->
                 graph_well_formed grph .


(* ###################################################### *)
(** * Max Flow / Min Cut: Axioms, Properties, Lemmas and Theorems *)

(*
  Let G(V,E) be a graph, and for each edge from u to v, let c(u,v) be the capacity 
  and f(u,v) be the flow. We want to find the maximum flow from the source s to the sink t. 
  After every step in the algorithm the following is maintained: *)

(** [capacity constraints]: The flow along an edge can not exceed its capacity
    (weight), such as:
 	forall (u, v) \in E , f(u,v) <= c(u,v)  *)

Axiom capacity_constraint : forall (a:adjacence) n c f, 
                        a = (n,c,f) -> 
                        f <= c.

(** [flow conservation]: The sum of all the flow that enters ("consumes") a 
    vertex [v], such as [v] is not the source (s) or sink (t) vertex, is equal 
    to the sum of all the flow that gets out ("produces").
         forall v \in G: \sum_{w \in v} = \sum_{w \out in v} *)

Axiom  flow_conservation: forall (grph :graph) (vn :VerName),
                       beq_internal_vertex grph vn = true ->
                       vertex_flow_out grph vn = vertex_flow_in grph vn.

(* Axiom path_nonneg : forall (v1:vertex) (v2:vertex) (n:Weight),  *)
(*                            (path v1 v2 n) -> (n >= 0). *)

(* Axiom path_inversion : forall (v1:vertex) (v3:vertex) (n:Weight),  *)
(*                        (0 <= n) -> (path v1 v3 (n + 1)) ->  *)
(*                        exists v2:vertex, (path v1 v2 n).  *)


(** * TODO *)

(** _Theorem_ [exists_max_flox]: forall graph [G], there is always a max-flow. 
     Use: excluded middle and prove by contradiction *)

(** _Theorem_ [flow_conservation_path]: forall path in graph [G], a path [p1] and [p2] such as [p2] \in [p1]
     then flow ([p2]) < capacity [p2] and flow ([p1]) >=  flow([p2]). *)

(** 
    Maybe?   
    _Theorem_ [skew_symmetry]: forall (u, v) \in E \ f(u,v) = - f(v,u) 	
     The net flow from u to v must be the opposite of the net flow from v to u. *)



(* ###################################################### *)
(** * Max Flow / Min Cut Algorithm *)

(*
  There is at least one edge incident to each node.

  augment(f, P)
    Let b = bottleneck(P,f)
    For each edge (u,v) \in P
      If e=(u,v) is a forward edge then
        increase f(e) in G by b
      Else
        decrease f(e) in G by b
      EndIf
    EndFor
    Return(f)

  Max-Flow
    Initially f(e) = 0 for all e \in Graph G
    While there is an s->t path in the residual Graphf
      Let P be a simple s->t path in Gf
      f' = augment(f,P)
      Update f to be f'
      Update the residual graph Gf to be Gf
    EndWhile
  Return f


*)


(** References:
    [1] Benjamin C. Pierce, Chris Casinghino, Marco Gaboardi, Michael Greenberg, 
        Catalin Hritcu, Vilhelm Sjoberg, and Brent Yorgey. Software Foundations. 
        Electronic textbook, 2013. http://www.cis.upenn.edu/ bcpierce/sf.

*)