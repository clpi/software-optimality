import MetricRelevance
open MetricRelevance
#guard indirectRate 7 10 [⟨1,7,7,10,10,true,100,90⟩,⟨2,8,8,10,10,true,100,100⟩] = some ⟨1,1⟩
#guard indirectRate 7 10 [⟨1,7,7,10,10,true,100,90⟩,⟨1,7,7,10,10,true,100,90⟩] = none
#guard indirectRate 7 10 [⟨1,7,7,10,10,false,100,90⟩] = none
#guard indirectRate 7 10 [⟨1,7,7,10,11,true,100,90⟩] = none
#guard indirectRate 7 10 [⟨1,7,7,10,10,true,100,100⟩] = some ⟨0,1⟩
#guard observedMixed 7 [⟨1,7,true⟩,⟨1,7,false⟩] = none
#guard observedMixed 7 [] = none
#guard observedMixed 7 [⟨1,7,true⟩] = some false
#guard observedFailureRate 7 [⟨1,7,false⟩] = some ⟨1,1⟩
#guard observedDisagreement 7 [⟨1,7,false⟩] = none
#guard partRates [1] [(0,1),(0,0),(0,1)] (fun _ a b => decide (a ≠ b)) (fun p a b => direct [0,1] fixtureValue fixtureIntent 0 p a b) = [(1,some ⟨1,1⟩)]
#guard partRates [1] [(0,1)] (fun _ _ _ => false) (fun _ _ _ => true) = [(1,none)]
#guard observedFailureRate 7 [⟨1,7,false⟩,⟨2,8,true⟩] = some ⟨1,1⟩
#guard observedDisagreement 7 [⟨1,7,true⟩,⟨2,7,true⟩,⟨3,7,true⟩,⟨4,7,false⟩,⟨5,7,false⟩] = some ⟨6,10⟩

#guard exactRate (contexts.map (fun c => decide (sharedRoot false c ≠ sharedRoot true c))) = some ⟨3,4⟩
