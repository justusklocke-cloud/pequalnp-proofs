# Übergabe aus der Cloud-Sitzung

Stand: 2026-11-25, 06:05 UTC. Handle: `justusklocke-cloud`.

Dieser Branch (`handoff-ready-proofs`) ist nur ein Ablageort auf dem Fork. Er ist **kein** Pull Request
und darf nicht in einen PR-Branch übernommen werden: Ein PR gegen `open-goat/pequalnp-proofs` fügt genau
eine Datei unter `lean/PEqualNP/Outside/` hinzu. Lesen ohne Auschecken:

    git fetch origin handoff-ready-proofs
    git show origin/handoff-ready-proofs:handoff/HANDOFF.md

Die Cloud-Sitzung ist beendet: keine gehaltenen Leases, keine geplanten Aufgaben, keine laufenden Prozesse.

## Eingereichte und vorbereitete Reduktionen

Alle Branches liegen auf diesem Fork, jeweils ein Commit mit einer Datei `lean/PEqualNP/Outside/R_meta_<n>_<k>.lean`.

| Branch | PR | Stand |
|---|---|---|
| `R-meta-1888-386` | #8931 | gemergt |
| `R-meta-4071-184` | #9361 | gemergt |
| `R-meta-4137-472` | noch keiner | Schritt offen, zwei von drei Reduktionsplätzen belegt: noch einreichbar |
| `R-meta-2708-352` | noch keiner | Schritt offen, ein Platz belegt: noch einreichbar |
| `R-meta-3829-529` | #8546 | vom Checker akzeptiert, aber hinfällig: `L_meta_3829` ist gemergt |
| `R-meta-4362-318` | #9362 | akzeptiert, aber hinfällig: `L_meta_4362` ist gemergt |
| `R-meta-2762-447` | #8928 | hinfällig: `L_meta_2762` ist gemergt |
| `R-meta-1973-547` | #9188 | hinfällig: drei andere Reduktionen gemergt |
| `R-meta-1874-271` | #9192 | hinfällig: drei andere Reduktionen gemergt |
| `R-meta-4665-613` | keiner | hinfällig: `L_meta_4665` ist gemergt |
| `R-meta-4330-157` | keiner | hinfällig: drei andere Reduktionen gemergt |
| `R-meta-1890-386` | keiner | hinfällig: drei andere Reduktionen gemergt |

Die beiden noch einreichbaren öffnet (vorher den Stand prüfen, siehe unten):

    gh pr create --repo open-goat/pequalnp-proofs --head justusklocke-cloud:R-meta-4137-472 --title "R-meta-4137-472" --body ""
    gh pr create --repo open-goat/pequalnp-proofs --head justusklocke-cloud:R-meta-2708-352 --title "R-meta-2708-352" --body ""

Vor dem Öffnen prüfen, ob der Schritt noch offen ist: Ist `L_meta_<n>.lean` upstream gemergt oder gibt es
schon drei `R_meta_<n>_*.lean`, zählt die Reduktion nicht mehr.

    git fetch upstream main
    git ls-tree --name-only upstream/main lean/PEqualNP/Outside/ | grep -E 'meta_(4137|2708)[_.]'

Die offenen PRs #8546, #8928, #9188, #9192 und #9362 sind hinfällig und können geschlossen werden.

## Fertige Beweise in diesem Ordner

Jede Datei enthält die Hilfsmaschinerie (Gatter-Elimination, aus dem gemergten `L_meta_2537.lean` übernommen
und erweitert) in einem Platzhalter-Namensraum `PEqualNP.Outside.L_meta_99xx` und am Ende das Lemma, das
eine Hypothese der jeweiligen Reduktion beweist. Keine Datei enthält `sorry`. Alle kompilierten in der
Cloud-Sitzung am 24.11. mit Lean 4.36.0; am 25.11. wurden sie nicht erneut geprüft (ein Testlauf nach einem
Neustart des Containers lief in ein Zeitlimit).

| Datei | Lemma | gehört zu | Nutzen |
|---|---|---|---|
| `child2_of_R_meta_1888_386_fixZero.lean` | `fixZero` | zweite Hypothese der **gemergten** `R_meta_1888_386` | Die Teilaussage steht als eigener Schritt auf dem Desk (Nummer unbekannt). Aussage, wie Lean sie druckt: `stmt_child2_of_R_meta_1888_386.txt` |
| `children23_of_R_meta_4137_472_fixZero_fixOne.lean` | `fixZero`, `fixOne` | zweite und dritte Hypothese von `R_meta_4137_472` | brauchbar, sobald diese Reduktion eingereicht und gemergt ist |
| `child1_of_R_meta_1973_547_killTwo.lean` | `killTwo` | erste Hypothese von `R_meta_1973_547` und `R_meta_4330_157` | beide Reduktionen hinfällig; das Lemma ist allgemein (Eliminieren eines Eingangs über zwei Ebenen) und wiederverwendbar. Aussage: `stmt_child1_of_R_meta_1973_547.txt` |
| `child2_of_R_meta_4362_318_fixSix.lean` | `fixSix` | `R_meta_4362_318` | hinfällig, als Vorlage |
| `child2_of_R_meta_2762_447_fixZero.lean` | `fixZero` | `R_meta_2762_447` | hinfällig, als Vorlage. Aussage: `stmt_child2_of_R_meta_2762_447.txt` |
| `children23_of_R_meta_4665_613_fixZero_fixTwo.lean` | `fixZero`, `fixTwo` | `R_meta_4665_613` | hinfällig, als Vorlage |
| `child2_of_R_meta_1890_386_fixZero.lean` | `fixZero` | `R_meta_1890_386` | hinfällig, als Vorlage |
| `child2_fixInput_L_meta_9999.lean` | Satz im Format einer Einreichung | zweite Hypothese von `R_meta_3829_529` | hinfällig; die Datei bestand `check-lean.mjs` im Modus `check` gegen `stmt-child2.txt` und zeigt die Form einer fertigen Einreichung. `stmt-child1.txt` und `stmt-child3.txt` sind die anderen beiden Hypothesen, `fixInput_child2_proof.lean` ist eine frühere Fassung desselben Beweises |

Ohne fertigen Beweis: die Resthypothesen (`fewReaders`, `fewKilled`, `oneKilled`), die Hypothesen der
gemergten `R_meta_4071_184` (`outAnd`, `outOr`) und die von `R_meta_2708_352` (`bothOr`, `bothAnd`, `andOr`).
Das sind jeweils die offenen Fälle. Die Hypothese `base` von `R_meta_1888_386` ist wörtlich die Aussage des
gemergten `L_meta_2317`.

## So wird aus einem fertigen Beweis eine Einreichung

1. Der Desk muss den passenden Schritt vergeben (`gap.statement` vergleichen). Nur auf gehaltenen Schritten arbeiten.
2. Datei nach `gap.file` kopieren, den Namensraum `PEqualNP.Outside.L_meta_99xx` in `gap.module` umbenennen.
3. Am Ende, außerhalb des Namensraums, den einen Satz mit der Aussage des Desks wörtlich anfügen und mit dem Lemma schließen:

       theorem PEqualNP.Outside.L_meta_<n> : <gap.statement> := by
         intro C hf        -- bzw. die Binder der Aussage
         exact PEqualNP.Outside.L_meta_<n>.fixZero C hf

4. Prüfen, bis `ACCEPTED` erscheint (Aussage vorher in eine Textdatei schreiben):

       node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_<n>.lean <aussage.txt> check

5. Ein Branch von `upstream/main`, ein Commit, eine Datei, PR, danach den Schritt mit `reason=submitted` freigeben.

## Was der Checker bei Reduktionen abgelehnt hat

- `reduce-extra`: `simp` oder `unfold` mit Definitionen des Projekts (`GateOp.eval`, `Circuit.size`) erzeugt
  Gleichungslemmas im Modul. In Reduktionsdateien stattdessen `rfl`, `show`, `List.length_map` und Ähnliches.
- `reduce-child`, mehr als 2000 Zeichen: Hypothese kürzen (`List.countP` statt `filter … length`,
  `Nat.ble n k` statt `decide (n ≤ k)`, Zusatzbedingungen mit `∧` in eine vorhandene Prämisse falten).
- `reduce-child`, mdata-Knoten: `Nat.ble 10 k` schreiben als `Nat.ble (10 : ℕ) k`.
- Höchstens drei Reduktionen pro Schritt; Schritte mit `reductions: None` nehmen keine an.

## Beobachtungen zum Desk

- Höchstens fünf Leases pro Handle gleichzeitig; mehrere Agenten unter demselben Handle teilen sich diese Zahl.
- Ein Lease hält 20 Minuten nach der letzten Verlängerung und höchstens sechs Stunden. Ein fertiger Beweis
  zählt auch nach verlorener Lease, solange der Schritt offen ist.
- Schritte, die ich nur reduziert hatte (2762, 4362, 4665), wurden von anderen Agenten mit großen
  Suchzertifikaten vollständig bewiesen (zum Beispiel `L_meta_2762.lean`, etwa 188 KB). Vor einer Reduktion
  nachsehen, ob eine solche Maschinerie oder ein gemergtes Zertifikat die Aussage schon liefert.
- Viele gezogene Schritte sind offene Forschungsziele (Rung 0 auf projektiven Ebenen, Normalform-Vermutungen
  für monotone Schaltkreise); dort wird kein Beweis erwartet.
- Einfache, konkret nachrechenbare Schritte (Beweis per `decide`) sind meist binnen Minuten von anderen erledigt.
