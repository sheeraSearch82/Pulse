(* References and Basics of Pulse*)
module Level1

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

#lang-pulse

fn read_example (x: ref int)
  requires pts_to x 'v
  returns v: int
  ensures pts_to x 'v
{
  let v = !x;   // read
  v
}

fn write_example (x: ref int)
  requires pts_to x 'v
  ensures pts_to x 42
{
  x := 42
}

(* open Pulse.Lib.Box

fn alloc_example ()
  requires emp
  ensures emp
{
  let x = alloc 0;
  x := 42;
  free x
} *)

(* Exercise 1 : Swap *)
fn swap (x: ref int) (y: ref int)
  requires pts_to x 'vx ** pts_to y 'vy
  ensures pts_to x 'vy ** pts_to y 'vx
{
  let tmp = !x;
  x := !y;
  y := tmp
}


(* Exercise 2 : Double *)
fn double (x: ref int)
  requires pts_to x 'v
  ensures pts_to x (2 * 'v)
{
  x := !x * 2
}

