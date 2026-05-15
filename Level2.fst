(* Operations on references*)
module Level2

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

#lang-pulse


(* Exercise 1: Write a function that takes two references and returns their sum, without modifying either: *)
fn add_refs (x: ref int) (y: ref int)
  requires pts_to x #0.5R 'vx ** pts_to y #0.5R 'vy
  returns r: int
  ensures pts_to x #0.5R 'vx ** pts_to y #0.5R 'vy ** pure (r = 'vx + 'vy)
{
   let vx  = !x;
   let vy  = !y;
   vx + vy
}

(* Exercise 2: Write a function copy that copies the value of x into y *)
fn copy (x: ref int) (y: ref int)
requires pts_to x #0.5R 'vx ** pts_to y 'vy
ensures pts_to x #0.5R 'vx ** pts_to y 'vx
{
  y := !x
}
