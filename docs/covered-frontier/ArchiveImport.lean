import EligibleCampaign
import Std
open EligibleCampaign
-- Generated from the pinned archived report; review.py verifies every byte.
-- qualification.json SHA256: 037ce2972cbf5bb72de79e24e3c914b4254406a488696a5e4e9f7b00eff50b73
-- policy.json SHA256: 44faa39b813fe8ff0571957fa2f535d2d6d022ebd765cf8c0d95296ef5d40416
example : times .O1 = [10769189848, 7296152413, 7966428370] := by decide
example : caps = [10769189848, 7296152413, 7966428370] := by decide
example : receiptFlags .O1 = [[(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)]] := by decide
example : workers .O1 = 1 := by decide
example : gate .O1 = true := by decide
example : cost .O1 0 = 10769189848 := by decide
example : times .O2 = [5429128102, 6128442901, 6240471073] := by decide
example : caps = [10769189848, 7296152413, 7966428370] := by decide
example : receiptFlags .O2 = [[(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)]] := by decide
example : workers .O2 = 2 := by decide
example : gate .O2 = true := by decide
example : cost .O2 0 = 6240471073 := by decide
example : times .R2 = [9146680841, 6480720115, 6777395883] := by decide
example : caps = [10769189848, 7296152413, 7966428370] := by decide
example : receiptFlags .R2 = [[(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)]] := by decide
example : workers .R2 = 2 := by decide
example : gate .R2 = true := by decide
example : cost .R2 0 = 9146680841 := by decide
