# What can be recovered about a historical run?

Given surviving evidence, this procedure can (1) establish every forced answer to a finite set of historical questions, (2) exhibit histories that still disagree, (3) publish a guess with a named prior, and (4) find all nondominated ways to obtain further observations and solve the resulting implications. The central condition is identifiability. A later observation establishes a historical answer exactly when the histories compatible with that observation agree on the answer.

## The ledger

A run key contains a system, revision, configuration, and occurrence ID. Repeated launches get distinct occurrence IDs. An atom pairs a question about a run with an exact value. In the CLI, occurrence has value 0 or 1. For an attribute, JSON null represents absence of the run, and integer 0 is an ordinary value. A missing model coordinate is rejected. An unknown answer is a diagnosis about multiple possible histories. It cannot be encoded as an observed null.

An immutable row carries its ID, body ID, append time, source, model version, route, list of joint premise atoms, one conclusion atom, and optional receipt. Events append either a row or a withdrawal of an ID. At any ledger prefix, a row is live exactly when its complete event was authorized, there is no authorized withdrawal of its ID, and all authorized uses of the ID agree on the entire row. An identical redelivery is idempotent. The ledger keeps withdrawn and conflicted events for replay. The live rows produce the hypergraph directly. Roots have receipts. Each accepted implication is one directed hyperedge from **all** its premises to its conclusion.

| Route tag | Publication and evidence rule |
|---|---|
| `discovery` | Add names from a roster or an entry's head or premises. A newly named run can still have occurrence 0. A wholly unnamed run requires an external source of names, a generator, or an existential question encoded by the domain. |
| `direct` | Admit a source-validated receipt for this exact occurrence and field. Check the complete atom, source and capture time against the row. |
| `backfill` | Import an original receipt later. Preserve both capture and append times. The recorder checks an independently supplied digest and retains the exact UTF-8 capture bytes. A digest authenticates bytes only to the extent its expected value and collector are trusted. |
| `sparse` | Recompute from the current snapshot without any prior cached conclusion. Emit a joint edge from verified root atoms to an answer shared by every compatible history. |
| `symbolic` | Admit a checked implication under the named model, including an empty-premise invariant. A model can force an answer even with zero observations. |
| `replay` | Scope the new execution to its own identity. A historical result requires a checked implication connecting replay evidence to the original question. |
| `transfer` | A declared version, platform, simulator, artifact, or domain mapping can supply an implication. It must preserve the specified answer under its joint assumptions. |
| `independentPrediction` | Append another program's proposed answer and source, or compute all minimum-loss guesses using the supplied prior. The route adds zero roots and zero inference rules. |
| `hookPlan` | Record intent to observe future runs. Arming the recorder emits a plan before running the child. |
| `hookSample` | A firing hook produces a receipt for the actual fresh occurrence. The example records child exit or signal status plus a symbolic equality rule for that same occurrence. |

Rows carry two separate four-valued colors, one against direct evidence and one against qualified closure. For the row's exact proposition, the support and opposition bits respectively mean that the proposition occurs and that a different answer to the same question occurs. The four names are **unknown** (00), **supported** (10), **opposed** (01), and **conflict** (11). A conjecture may match a supported fact. Its advisory route still contributes no support. A global inconsistency can involve distinct questions with no single locally conflicted color. An empty survivor set disables the qualified closure entirely.

## Recovery theorem and procedure

Let $W$ be the candidate histories, $m(w,q)$ the answer in history $w$, and $B$ the live, verified root atoms. Compute the compatible histories

$$
F(B)=\{w\in W\mid \forall(q,v)\in B,\ m(w,q)=v\}.
$$

1. If $F(B)$ is empty, return **inconsistent**. Both bad receipts and incomplete models can cause this result. The checker publishes no inferred historical answer.
2. If two members give different answers to $q$, return **ambiguous** with both histories as witnesses. With positive total weight, prediction may additionally return every candidate value minimizing the sum of the weights of the histories on which that value is wrong. Zero total weight yields no guesses.
3. Otherwise the nonempty set agrees on a value $v$. Publish the hyperedge $B\to(q,v)$ with its model version, or reuse the already derivable answer. The batch uses fresh authorized IDs and can cover all supplied questions in one append. Every premise is rechecked on replay. A withdrawal removes the support it owned. Other genuine derivations may keep the same conclusion alive.

**Exactness.** Filtering gives `survivors_exact`. Inspecting the first survivor and searching for a disagreement gives `diagnose_exact` and `ambiguous_witness`. A complete uniformity check makes the new edge valid in every modeled history whenever its parents hold, since the history then belongs to the set on which uniformity was checked. Induction on a rooted derivation proves that every qualified conclusion is true in every survivor. Conversely a unanimous requested conclusion either already has a derivation or is added by this batch. The append-admission lemma preserves all previous live rows and admits each fresh one. Consequently, after actual ledger publication, for every requested $q$ and value $v$,

$$
(q,v)\in\mathrm{closure}_{\rm after}
\quad\Longleftrightarrow\quad \forall w\in F(B),\ m(w,q)=v
\qquad(F(B)\ne\varnothing).
$$

This is `published_batch_exact`. `bet_exact` proves optimality under the declared weighted zero-one loss. That result depends on the prior. It supplies no empirical calibration guarantee. `registered_sound` also accepts a Lean proof over any type of histories, including infinite ones. The included zero-measurement example proves a predicate at every natural input. Its finite ledger needs only one proof-bearing rule.

For a physical claim, `transport_recovery` requires a map from every admissible real history into the model that preserves the evidence and the requested quantity, plus the truth of the receipts for the actual history. A finite quotient may suffice even for an infinite system. In particular a missed possible exception can turn a model-unanimous value into a wrong physical answer.

## Which observations are sufficient?

For evidence function $O$ and historical question $Q$, an exact decoder on possible histories exists iff $O(x)=O(y)\Rightarrow Q(x)=Q(y)$ for all possible $x,y$. Necessity follows by applying the decoder to the shared input. For sufficiency, choose any representative of each nonempty observation class. All representatives give the same answer. `factorization` establishes existence over arbitrary types. `decode` computes the answer on an explicit finite table. This argument also covers an independent program with arbitrary internal computation. If the inputs supplied to it are identical, an exact claim that differs between the two histories cannot follow from those inputs.

For a finite catalogue of deterministic Boolean probes, model the joint past and future in each history. A policy tree can stop or choose its next probe from the previous answers. **Some finite policy resolves every requested question iff every pair of histories that agrees on all available probes also agrees on every requested answer.** Induction on the policy shows that an indistinguishable pair takes the same branches at every depth. In the other direction, reading each probe once supplies a witness. `full_observability_iff` proves both directions. A single future probe may be informative about the past if the joint model establishes that coupling. In the absence of that coupling, measuring it on another run leaves the ambiguity intact.

## Computing the Pareto frontier and instantiating the answers

1. Declare the possible histories, target questions, attainable probes, maximum depth, candidate proof engines, and hard feasibility constraints. Each engine supplies a proof of agreement with the worklist closure on bounded inputs. Probe availability and physical costs are inputs. CLI sensor availability labels describe where the readings would come from. The CLI enumerates hypothetical policies and does not dispatch sensors.
2. Enumerate **all** stop/probe binary decision trees up to depth $d$. With $s$ sensors there are $N_0=1$ and $N_{d+1}=1+sN_d^2$ syntactic candidates. `plans_exact` follows by structural induction. `boundedCount_exact` permits refusal before enumeration when the declared search cap would be exceeded.
3. Retain a separate binary loss coordinate for each named pair of histories and question on which they disagree. Its loss is 1 when the policy fails to distinguish the pair. Add resource costs and enforce hard constraints. The CLI uses worst-path cost and worst-path read count, and optionally requires all questions resolved. The Lean API accepts joint engine/policy constraints and costs, including interactions.
4. In the finite product of engines and policies, retain a feasible member iff no feasible competitor weakly improves every coordinate and strictly improves at least one. The pairwise filter, with enumeration completeness, proves `joint_exact`. Equal-cost policies with different identities survive. The observation-only special case is `optimal_exact`. The reference enumeration can grow doubly exponentially with depth. The proof establishes frontier membership, while the time needed to compute it remains a separate engineering cost.
5. After taking the chosen path, the domain adapter must supply receipts that entail each realized reading. `realized_path` proves by induction that matching those readings reproduces that path, even when other branches would read different sensors. With a full-resolution frontier requirement and a modeled actual history consistent with the receipts, `joint_publication` proves that after the batch append the **selected engine** derives the requested value iff it equals the actual history's model value. Independently, `engine_instantiates_exactly` proves that both included engines compute exactly every rooted finite Horn consequence, including joint premises, multiple supports, and cycles with an independent root.

The completeness statements quantify over declared worlds, questions, rule forms, sensors, policies and engines. They cover arbitrary domain semantics through the interfaces. The concrete JSON adapter uses explicit finite tables, natural-valued attributes and deterministic side-effect-free probe readings. A domain with missing values on existing runs needs its own value encoding. A stochastic, destructive or state-changing instrument needs an explicit transition/outcome model and an appropriate policy/cost proof before using these planner guarantees. Universal runtime optimality, acquisition of a missing physical record, and completeness of a real deployment's world catalogue are separate claims.

## Reproduce the execution

With Lean 4.19.0, Lake and Python 3 available, run from the repository root.

```sh
lake --wfail build
sh check.sh
python3 examples/history_roundtrip.py --replay examples/history-recording.json
python3 examples/history_roundtrip.py
```

The first Python command rechecks a saved real capture at three ledger prefixes. It also clears every receipt, derives a model invariant with an empty-premise edge, then adds a countermodel and checks that the invariant becomes ambiguous. The second launches two new processes under distinct run IDs, withholds the original capture, invokes a separate predictor, imports the archived bytes, and withdraws their support. Both processes actually return status 7. The prior favors status 9 with weight 8, status 7 with weight 2, and no occurrence with weight 1. The old run is absent from the starting roster.

| Ledger prefix | Compatible historical possibilities | Recovered old values | Full-resolution observation frontier |
|---|---|---|---|
| Later hook and independent prediction | Absent, exit 7, exit 9 | Each of the three questions is ambiguous. Status prediction is 9. | Six nondominated trees among 19 enumerated, using two modeled retained-index probes |
| Original archived receipt admitted | Exit 7 | Occurred = 1, status = 7, status-equals-7 = 1 | Stop, zero reads |
| Original receipt withdrawn | Absent, exit 7, exit 9 | Historical conclusions lose support. The later run keeps its own receipt. | Same unresolved possibilities as the first prefix |

Two concurrent audits publish respectively two and zero new proof rows, in either order. The test also checks malformed archive digests, byte-exact export of differently formatted captures, idempotent retry and refusal when the enumeration cap is reduced to 18. The retained-index probes and their costs are modeled. Only the child executions and capture operations were exercised physically.

To collect a new receipt, arm a hook, then pass its returned numeric plan ID to the recorder. For example, on a fresh database the first ID is zero.

```sh
python3 tools/history.py --db runs.db arm --system build --revision r1 --configuration demo --model exit-schema-1 --equals 7
python3 tools/history.py --db runs.db run 0 -- python3 -c 'raise SystemExit(7)'
```

The remaining commands are `export DIGEST`, `archive FILE --sha256 DIGEST`, `suggest ATOM.json --source SOURCE --model PRIOR`, `audit CAMPAIGN.json`, and `withdraw ID`. The command-line adapter treats the owner of its SQLite database as the authorizing principal. A collector crash before durable capture can leave a run unobserved. The hook covers the launched child process's return status.

For stateless use, `.lake/build/bin/historyaudit INPUT.json` reads a campaign with `model`, `prior`, `worlds`, `roster`, `questions`, optional `planning`, and the snapshot fields `stamp`, `ledger`, `authorized`, `verifiedReceipts`. Use the saved recording's `campaign` object and the replay example for the exact wire representation. The output contains historical events and live flags, typed and colored hyperedges, countermodel names, computed guesses, new appendable events, the qualified closure, and the finite observation frontier. The joint engine selector and proof registration interfaces are available from Lean.
