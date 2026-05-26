# Übersicht
Die DOJ.thy Datei ist von Mattias

Meine Definitionen befinden sich in defDS.thy. Sie habe sich zum letzten Mal semantisch nicht geändert.

Die Theoreme befinden sich in theoremsDS.thy.

In wtDS.thy befinden sich Versuche dojs als Wahrscheinlichkeiten aufzufassen.


## Zu den Theoremen
Ich konnte noch keine strengen Monotonien zeigen. Ein Lemma hat noch ein "sorry". Beim Hinzufügen von unabhängigen Argumenten, findet Isabelle ein Gegenbeispiel.

## Zu den dojs als Wahrscheinlichkeiten
Zuerst habe ich versucht, die bestehende Theorie zu zeigen. Da fehlt nur noch die schwierige Richtung der "Sigma-Additivität".

Am 13.05. hatten wir überlegt, ob dojs unter der Vereinigung abgesclossen sind <-> ob die Modelle unter der Vereinigung abgesclossen sind.

Explizit: ∀P Q. ∃C. mods P ds ∪ mods Q ds = mods C ds
Das scheint nicht zu funktionieren.


Der doj einer Position scheint ebenfalls nicht die Summe der dojs seiner Literale zu sein: doj P ds ≠ (∑l ∈ P . doj {l} ds)
