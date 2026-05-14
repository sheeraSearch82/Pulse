module Level3

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

(*Exercise 1: max
  Write a function that sets x to the maximum of x and y (y read-only): *)
 fn rec max_ref (x: ref int) (y: ref int)
 requires pts_to x 'vx ** pts_to y #0.5R 'vy
 ensures  pts_to x (if 'vy < 'vx then 'vx else 'vy) ** pts_to y #0.5R 'vy
{
   let vx = !x;
   let vy = !y;
   if (vy < vx)
   {
       ()
   }
   else
   {
       x := vy
   }
   
}

(* Exercise 2: count_down
   Write a loop that counts x down to zero: *)
  fn count_down (x: ref int)
  requires pts_to x 'v ** pure ('v >= 0)
  ensures pts_to x 0
{
  while (
    let v = !x;
    (v > 0)
  )
  invariant exists* v. pts_to x v ** pure (v >= 0)
  {
    let v = !x;
    x := v - 1
  }
}
  
let rec factorial_spec (n: nat) : nat =
  if n = 0 then 1 else n * factorial_spec (n - 1)

(* Exercise 3 (challenge): factorial
Write a recursive function that computes n! and stores it in x *)

fn rec factorial (x: ref int) (n: nat)
  requires pts_to x 1
  ensures pts_to x (factorial_spec n)
  {
    if (n = 0) 
    {
      ()
    }
    else
    {
      factorial x (n - 1);
      let v = !x;
      x := n * v
    }
      
  }


