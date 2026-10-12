import Ariadne
import Ariadne.Shallow.Safety

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Tests.Int53
open Ariadne

private def checks : List (String × Bool) := [
  ("function f(x: Int53): Int53 { return x + 1; }", true),
  ("type Size = Int53; function f(x: Size): Int53 { return x; }", true),
  ("function f(x: Int53): number { return x / 2; }", true),
  ("function f(x: Int53): Int53 { return x / 2; }", false),
  ("function f(x: number): Int53 { return x; }", false),
  ("function f(): Int53 { let x = 0; x = 0.5; return x; }", false),
  ("function f(): number { let x: number = 0; x = 0.5; return x; }", true),
  ("function f(x: Int53): Int53 { return Math.floor(x / 2); }", true),
  ("function f(x: Int53): Int53 { return Math.trunc(x / 2); }", true),
  ("function f(x: Int53): Int53 { return Math.min(x, 2); }", true),
  ("function f(): Int53 { return 9007199254740991; }", true),
  ("function f(): Int53 { return 9007199254740992; }", false),
  ("function f(): Int53 { return 100e-2; }", true),
  ("function f(): Int53 { return 101e-2; }", false),
  ("function f(xs: readonly string[]): Int53 { return xs.length; }", true)]

theorem frontend_refinement : checks.all (fun (source, accepted) =>
    (frontend ("type Int53 = number; " ++ source)).isOk == accepted) = true := by kernel_rfl

theorem reserved_alias : (frontend "type Int53 = bigint; function f(): bigint { return 0n; }").isOk = false := by
  kernel_rfl

end Tests.Int53
