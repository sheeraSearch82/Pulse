(* Data Structures in Pulse *)
module Level4

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

#lang-pulse

open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Array.Core
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn array_sum (a: array int) (n: SZ.t)
  requires pts_to a 'vs ** pure (SZ.v n = Seq.length 'vs) (* 'vs is the functional equivalent of the array a *)
  returns r: int
  ensures pts_to a 'vs
{
  let mut sum = 0;
  let mut i = 0sz;
  while (
    let iv = !i;
    SZ.lt iv n      (* SZ.lt ---> less than operator of SZ type *)
  )
  invariant exists* iv sv.  (* array index variable and sum variable keeps on changing *)
    Pulse.Lib.Reference.pts_to i iv **  (* the invariant is that the variables maintain their points-to relationships *)
    Pulse.Lib.Reference.pts_to sum sv ** 
    pts_to a 'vs ** pure (SZ.v iv <= SZ.v n) 
  {
    let iv = !i;
    let v = a.(iv);  (* Access a[i]*)
    let sv = !sum;   (* read the value of sum *)
    sum := sv + v;   (* add the value to the sum *)
    i := SZ.add iv 1sz (* increment the index *)
  };
  !sum (* return the final sum *)
}




fn array_fill (a: array int) (n: SZ.t) (v: int)
  requires pts_to a 'vs ** pure (SZ.v n = Seq.length 'vs)
  ensures exists* s. pts_to a s ** pure (Seq.length s = SZ.v n) ** 
          pure (forall (i: nat). i < Seq.length s ==> Seq.index s i = v)
{
  let mut i = 0sz;
  while (
    let iv = !i;
    SZ.lt iv n
  )
  invariant exists* iv s.
    Pulse.Lib.Reference.pts_to i iv **
    Pulse.Lib.Array.PtsTo.pts_to a s **
    pure (SZ.v iv <= SZ.v n) **
    pure (Seq.length s = SZ.v n) ** 
    (* Pulse cannot prove that j < Seq.length s based on the current invariant in the absence of 
       explicit (j < Seq.length s) *)
    pure (forall (j: nat). j < SZ.v iv ==> (j < Seq.length s /\ Seq.index s j = v))
  {
    let iv = !i;
    a.(iv) <- v;
    i := SZ.add iv 1sz
  }
}

(* Exercise: array_max
   Write a function that finds the maximum element in an array and returns it: *)
fn array_max (a: array int) (n: SZ.t)
  requires Pulse.Lib.Array.PtsTo.pts_to a 'vs ** 
           pure (SZ.v n = Seq.length 'vs) **
           pure (SZ.v n > 0)
  returns r: int
  ensures Pulse.Lib.Array.PtsTo.pts_to a 'vs **
          pure (forall (i: nat). i < Seq.length 'vs ==> Seq.index 'vs i <= r)
  {
    let mut max = a.(0sz);
    let mut i = 1sz;
    while (
       let iv = !i;
       SZ.lt iv n
    )
    invariant exists* iv m.
    (* 3 references are interseting here, the loop index, the max storage variable and the array itself *)
      Pulse.Lib.Reference.pts_to i iv **
      Pulse.Lib.Reference.pts_to max m **
      Pulse.Lib.Array.PtsTo.pts_to a 'vs **
      (* The invariant should say, the loop index will never exceed the array bounds *)
      pure (SZ.v iv <= SZ.v n) **

      (* This is the invariant that helps to prove the correctness condition *)
      (* During the process, the max value is always the maximum of the elements seen so far *)
      pure (forall (j: nat). j < SZ.v iv ==> (j < Seq.length 'vs /\ Seq.index 'vs j <= m))
    {
      let iv = !i;
      let v = a.(iv);
      let m = !max;
      if (v > m)
      {
        max := v
      };
      i := SZ.add iv 1sz
    };
    !max
  }

(* Exercise 3: Abstract predicate with is_stack, push and pop *)
(*  Modeling a stack by its height (how many items are on it). The ref int stores the count, not the actual elements *)

let is_stack (r: ref int) (top: int) : slprop =
  Pulse.Lib.Reference.pts_to r top ** pure (top >= 0)

(* When Pulse sees is_stack r 'top in a precondition, it treats it as an opaque predicate.
   It doesn't automatically look inside. So you can't directly read r because Pulse doesn't 
   know is_stack r 'top contains pts_to r top.
   You need to unfold it to reveal the underlying pts_to *)
   (*
       Step                       What Pulse sees
       -------------------       ----------------------
       Start                     is_stack r 'top — opaque
       After unfold              pts_to r 'top ** pure ('top >= 0) — visible   
       After r := v+1.           pts_to r v ** pure ('top >= 0) ** pure (v + 1 = 'top + 1) — visible   
       After fold                is_stack r ('top + 1) — opaque again         
   
    *)
fn push (r: ref int)
  requires is_stack r 'top
  ensures is_stack r ('top + 1)
{
  unfold is_stack r 'top;
  let v = !r;
  r := v + 1;
  fold (is_stack r ('top + 1));
}

fn pop (r: ref int)
  requires is_stack r 'top ** pure ('top > 0)
  ensures is_stack r ('top - 1)
{
  unfold is_stack r 'top;
  let v = !r;
  r := v - 1;
  fold (is_stack r ('top - 1));
}

(* Key Takeaways from Level 4
----------------------------------
(1) pts_to a 'vs — owns entire array, 'vs is a Seq.seq
(2) a.(i) — read at index, a.(i) <- v — write at index
(3) Indices are SZ.t, literals are 0sz, 1sz etc.
(4) When both Reference and Array are open, qualify pts_to explicitly
(5) let mut x = v — local mutable variable, no alloc/free needed
(6) exists* x y. — quantify multiple variables in one exists*
(7) Abstract predicates — hide implementation details behind a named slprop
       unfold — reveals the definition of an abstract predicate
       fold — hides it back
 F* lemmas can be called from Pulse to close pure proof obligations
 *)