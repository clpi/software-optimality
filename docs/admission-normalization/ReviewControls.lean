import AdmissionTests
open Admission AdmissionTests
-- An unauthorized conflicting payload cannot quarantine a valid claim.
def denyQ (e : Event) : Bool := e != .claim ka q
#guard checkLive denyQ [c,.claim ka q] ka p
#guard normalized yes [c,c] == normalized yes [c]
#guard !(checkLive yes [c,d,.claim newID p,.withdraw newID] newID p)
-- Multiple lineages' identical support IDs remain separate records.
#guard (normalized yes [c,.claim kb p]).length == 2
#guard (normalized yes [c,.claim kb p,d]).length == 1
#guard checkLive yes [c,.claim kb p,d] kb p
-- Collision quarantine cannot be evaded by repeating an original payload.
#guard !(checkLive yes [c,.claim ka q,c,c] ka p)
-- Explicit boundary: content is extensional, list order is not canonical bytes.
#guard normalized yes [c,.claim kb p] != normalized yes [.claim kb p,c]
