<link rel="stylesheet" type="text/css" href="pandoc.css"/>

SAT řešič
=========

Je daná množina množin literálů, kde v každé vnitřní množině je potřeba splnit alespoň jeden literál.

Implementace
------------

Program je napsán v jazyce Rust. To je relativně nový jazyk. V rychlosti se mu daří konkurovat nízkoúrovnovým jazykům (ve většině benchmarcích vychází o trošku hůře než C++), ale píše se v něm spíše tak, že se to podobá vysokoúrovnovým. Má propracovaný pamětový model, a tak je to jeden z mála jazyků, který je pamětově bezpečný a zároveň nemá garbage collector.

Program se zkompiluje pomocí pomocného programu `cargo`, který je běžnou součástí jazyka. Funguje na stabilní verzi Rustu. Vybuildí se pomocí příkazu `cargo build --release` (to release je důležité kvůli optimalizacím, neoptimilizované programy jsou v rustu velmi pomalé).

Ukázkový výstup:
```
$ ./target/release/sat-solver wufs/wuf-A/wuf100-430-A1/wuf100-0238-A.mwcnf
425 -1 2 -3 4 5 6 -7 8 9 10 11 12 -13 -14 15 -16 17 -18 19 20 -21 -22 -23 -24 -25 -26 -27 -28 29 -30 31 32 -33 -34 -35 -36 -37 -38 39 -40 41 42 43 -44 45 46 47 -48 -49 -50 -51 52 -53 -54 -55 56 -57 58 59 -60 61 62 -63 64 -65 -66 -67 68 69 70 -71 72 73 74 75 -76 77 78 79 -80 81 82 -83 -84 85 86 87 -88 -89 -90 91 92 93 94 95 -96 97 -98 -99 -100 0
time: 3.0738ms
0.0030738
```

Architektura
------------

Základní architektura je CDCL řešič s efektivní implementací propagace, která je inspirována řešičem MiniSAT. Jednotlivé reprezentace nejsou tak vymazlené jako jsou MiniSAT, takže rychlostí se mu nejspíše neblížim.

Na základních (splnitelných) problémech ze stránky https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html funguje na velikosti cca. 200 proměných většinou do minuty (Počáteční implementace bez jakékoliv heuristiky).

Účení nových klauzilí
---------------------

Bylo by pěkné moct se učit spoustu klauzulí a promazávat je, ale tenhle přístup je relativně náročný. Tak jsem zvolil, že budu mít poměrně přísný pravidla k naučení nové klauzule.

Aktuální pravidla jsou:

 - při příliš mnoha konfliktech se ani nesnaží učit
 - klauzule, která by měla víc než 5 literálů, tak se nenaučí
 - klauzule by měla být vyhodnotitelná z co nejvíce zafixovaných proměných
 - jednotlivý literály se zaměnují tak aby bylo možné dřív najít konflikt
 - např v $x_0 ∨ x_1 ∨ x_2$ a víme $¬x_2 ∨ x_3 ∨ x_4$ (z toho plyne $x_2 ⇒ x_3 ∨ x_4$), tak $x_2$ nahradíme a máme novou klauzuli $x_0 ∨ x_1 ∨ x_3 ∨ x_4$ (tohle opakuju dokud si myslím, že to má smysl)

Bylo by asi fajn ty parametry učení dát parametrizovatelný, nicméně aktuálně nejsou.

Pravidla jsou vybraný tak, aby se neučilo příliš hodně klauzulí a když už se nějaká naučí, tak aby měla přínos.

Selekční heuristika
-------------------

Heuristika která vybírá další proměné pro přiřazení bude hlavní věc, co se budu snažit ladit. Její implementace je nezávislá na solveru a je možné ji jednoduše nahrazovat.

Naivní vybírací heuristika - vybere první volnou proměnou co najde a tý přiřadí takovou hodnotu, aby způsobila co nejméně konfliktů. (Implementovaná)

Hladová váhová heuristika - vybere proměnou s největší váhou jako true a takto postupuje. Pravděpodobně v průběhu způsobí konflikt a nějakou proměnou to prohodí v důsledku.

Hladová váhová heuristika s prořezáváním - postupuje stejnějak Hladová váhová heuristika, akorát počítá maximální dosažitelnou váhu a když je horší než už nalezená, tak provede ořez. (Implementovaná)

Hladová váhová heuristika s prořezáváním
----------------------------------------

Vlastně už tahle jednoduchá heuristika fungovala natolik dobře, že nejtěžší problémy z sady wuf-A nalezne nejlepší řešení řádově v milisekundách, tak není nutné vymýšlet lepší heuristiky. Ještě jsem ani nezačal ořezávavat agresivněji prostor, tak nalezené řešení je zaručeně nejlepší.


Výsledky
--------

Byla použita hladová váhová heuristika s prořezáváním.

Tabulka s deaktivovaným učením:

| sada                      | průměrný čas | maximální čas |
|---------------------------|-----------:|-----------:|
| `wuf20-78-N1`             |   $60,4 µs$ |  $128,1 µs$ |
| `wuf50-201-N1`            |  $307,9 µs$ |   $3,01 ms$ |
| `wuf75-310-N1`            |   $1,35 ms$ |   $5,29 ms$ |
| `wuf20-78-M1`             |   $61,2 µs$ |  $139,0 µs$ |
| `wuf50-201-M1`            |  $306,5 µs$ |   $2,34 ms$ |
| `wuf75-310-M1`            |   $1,34 ms$ |   $5,72 ms$ |
| `wuf20-78-Q1`             |  $108,9 µs$ |  $276,6 µs$ |
| `wuf50-201-Q1`            |   $2,35 ms$ |   $9,65 ms$ |
| `wuf75-310-Q1`            |   $27,6 ms$ |  $102,1 ms$ |
| `wuf20-78-R1`             |  $107,7 µs$ |  $346,9 µs$ |
| `wuf50-201-R1`            |   $2,37 ms$ |   $13,5 ms$ |
| `wuf75-310-R1`            |   $27,6 ms$ |  $105,7 ms$ |
| `wuf20-88-A1`             |   $72,5 µs$ |  $226,6 µs$ |
| `wuf20-91-A1`             |   $69,1 µs$ |  $198,1 µs$ |
| `wuf100-430-A1`           |   $8,31 ms$ |   $60,7 ms$ |

Tabulka s aktivovaným učením:

| sada                      | průměrný čas | maximální čas |
|---------------------------|-----------:|-----------:|
| `wuf20-78-N1`             |   $71,1 µs$ |  $199,9 µs$ |
| `wuf50-201-N1`            |  $330,1 µs$ |   $2,68 ms$ |
| `wuf75-310-N1`            |   $1,39 ms$ |   $5,78 ms$ |
| `wuf20-78-M1`             |   $70,0 µs$ |  $188,9 µs$ |
| `wuf50-201-M1`            |  $329,7 µs$ |   $3,29 ms$ |
| `wuf75-310-M1`            |   $1,41 ms$ |   $6,53 ms$ |
| `wuf20-78-Q1`             |  $135,7 µs$ |  $470,7 µs$ |
| `wuf50-201-Q1`            |   $2,59 ms$ |   $10,2 ms$ |
| `wuf75-310-Q1`            |   $27,4 ms$ |   $83,9 ms$ |
| `wuf20-78-R1`             |  $135,5 µs$ |  $400,0 µs$ |
| `wuf50-201-R1`            |   $2,57 ms$ |   $10,8 ms$ |
| `wuf75-310-R1`            |   $27,3 ms$ |   $81,9 ms$ |
| `wuf20-88-A1`             |   $69,7 µs$ |  $152,9 µs$ |
| `wuf20-91-A1`             |   $68,4 µs$ |  $434,3 µs$ |
| `wuf100-430-A1`           |   $8,79 ms$ |   $67,0 ms$ |

Během vyhodnocování jsem narazil na chybu v učení klauzulí - ta byla odstraněna. Tím najde můj řešič optimální řešení pro všechny zadané problémy s maximálním časem $105,7 ms$.

Výsledky samotného učení jsou rozpoluplné. Někde lehce pomohlo, jinde to jen spomalovalo.

Mnou nalezené optimální řešení jsou ve složce `optimal_solutions`.

Závěr
-----

Návaznost na zadané metody je taková, že naučené klauzule tvoří tabu, kam se řešič už nebude přístě koukat. Rychlost je taková, že je těžké na něm ladit jednotlivé nastavení. Zkusil jsem vypnout učení a výsledky jsou nepřesvědčivé v tom, jestli to vůbec pomáhá.

Je zde prostor pro vylepšení, například ořezávání je celkem naivní. Nicméně rychlost je tak velká, že mě to nepřijde nutné.