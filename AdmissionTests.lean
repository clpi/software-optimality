import Admission
namespace AdmissionTests
open Admission

def ka : Key := ⟨1,101,8,1001⟩
def kb : Key := ⟨2,101,8,1001⟩
def newID : Key := ⟨1,101,8,1002⟩
def otherScope : Key := ⟨1,101,9,1001⟩
def p : Payload := ⟨42,true,900⟩
def q : Payload := ⟨42,false,901⟩
def yes (_ : Event) := true
-- Deliberately denied withdrawals: a concrete fixed authorizer for these tests.
def claimsOnly : Event → Bool | .claim _ _ => true | .withdraw _ => false

def c := Event.claim ka p
def d := Event.withdraw ka
#guard checkLive yes [] ka p == false
#guard checkLive yes [c] ka p == true
#guard (normalized yes [c,c,c]).length == 1
#guard checkLive yes [c, .claim ka q] ka p == false
#guard checkLive yes [c, .claim ka q] ka q == false
#guard (normalized yes [c, .claim ka q]).length == 0
#guard checkLive yes [c,d] ka p == false
#guard checkLive yes [d,c] ka p == false
#guard checkLive yes [c,d,c] ka p == false
#guard checkLive claimsOnly [c,d] ka p == true
#guard checkLive yes [c] kb p == false
#guard checkLive yes [c,.withdraw kb] ka p == true
#guard checkLive yes [c,.claim kb q] ka p == true
#guard checkLive yes [c,.claim otherScope q] ka p == true
#guard checkLive yes [c,d,.claim newID p] newID p == true
#guard (normalized yes [c,d,.claim newID p]).length == 1
#guard (normalized yes ([c] ++ [d])).length == 0
-- Counterexample: unioning already-normalized snapshots retains stale support.
#guard (normalized yes [c] ++ normalized yes [d]).length == 1
-- Hash/content identity is not a license to erase lineage or scope.
example : ka.content = kb.content := by decide
example : ka ≠ kb := by decide
-- A collision cannot be resolved by whichever payload arrived last.
example : checkLive yes [.claim ka q,c] ka p = false := by decide
example : checkLive yes [c,.claim ka q] ka p = false := by decide
-- Authorization is a theorem premise and executable input, not assumed policy.
example : checkLive claimsOnly [d,c] ka p = true := by decide
end AdmissionTests
