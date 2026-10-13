import V2

/-
function max(a: bigint, b: bigint): bigint {
  if (a < b) { return b; }
  return a;
}
function clamp(x: bigint, lo: bigint, hi: bigint): bigint {
  const y = max(x, lo);
  return y > hi ? hi : y;
}
-/
namespace V2Tests.Hand
open V2

def ast : Program := [
  { name := "max", params := ["a", "b"], body := [
      .ite (.binary .lt (.var "a") (.var "b")) [.ret (.var "b")] [],
      .ret (.var "a")] },
  { name := "clamp", params := ["x", "lo", "hi"], body := [
      .const "y" (.call "max" [.var "x", .var "lo"]),
      .ret (.cond (.binary .gt (.var "y") (.var "hi")) (.var "hi") (.var "y"))] }]

def sig_max : Sig := { name := "max", params := [("a", .int), ("b", .int)], result := .int }
def sig_clamp : Sig := { name := "clamp", params := [("x", .int), ("lo", .int), ("hi", .int)], result := .int }

def typed : TProgram [sig_clamp, sig_max] :=
  .cons sig_clamp
    (.const "y" (.call (Φ := [sig_max]) .here (.cons (.var .here) (.cons (.var (.there (by decide) .here)) .nil)))
      (.ret (.cond (.gt (.var .here) (.var (.there (by decide) (.there (by decide) (.there (by decide) .here)))))
        (.var (.there (by decide) (.there (by decide) (.there (by decide) .here)))) (.var .here)) .nil))
    (.cons sig_max
      (.ite (.lt (.var .here) (.var (.there (by decide) .here))) (.ret (.var (.there (by decide) .here)) .nil) .nil
        (.ret (.var .here) .nil))
      .nil)

theorem erased : typed.erase = ast := by rfl
theorem wf : typed.WF := by decide

def «max» (a b : Int) : Int := if decide (a < b) then b else a
def «clamp» (x lo hi : Int) : Int := let y := «max» x lo; if decide (hi < y) then hi else y

theorem max_eq (a b : Int) : «max» a b = (FVar.there .here : FVar _ "max" sig_max).get typed.denote (a, b, ()) := rfl
theorem clamp_eq (x lo hi : Int) :
    «clamp» x lo hi = (FVar.here : FVar _ "clamp" sig_clamp).get typed.denote (x, lo, hi, ()) := rfl

theorem max_source (a b : Int) :
    Converges (fun n => call ast n "max" [.bigint a, .bigint b]) (.ok (.bigint («max» a b))) := by
  have h := adequacy typed wf (FVar.there .here : FVar _ "max" sig_max) (a, b, ())
  rw [erased, ← max_eq] at h
  exact h

theorem clamp_source (x lo hi : Int) :
    Converges (fun n => call ast n "clamp" [.bigint x, .bigint lo, .bigint hi]) (.ok (.bigint («clamp» x lo hi))) := by
  have h := adequacy typed wf (FVar.here : FVar _ "clamp" sig_clamp) (x, lo, hi, ())
  rw [erased, ← clamp_eq] at h
  exact h

/-- A property proved on the readable definition transfers to every run. -/
theorem clamp_le (x lo hi : Int) (h : lo ≤ hi) : «clamp» x lo hi ≤ hi := by
  simp only [«clamp», «max»]; split <;> split <;> simp_all <;> omega

#eval call ast 10 "clamp" [.bigint 7, .bigint 1, .bigint 5]

end V2Tests.Hand
