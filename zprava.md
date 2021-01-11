<link rel="stylesheet" type="text/css" href="pandoc.css"/>

SAT řešič
=========

Je daná množina množin literálů, kde v každé vnitřní množině je potřeba splnit alespoň jeden literál. Úkolem je najít takové přiřazení do proměných, aby splňovali tuto podmínku.

Implementace
------------

Program je napsán v jazyce Rust. To je relativně nový jazyk. V rychlosti se mu daří konkurovat nízkoúrovnovým jazykům (ve většině benchmarcích vychází o trošku hůře než C++), ale píše se v něm spíše tak, že se to podobá vysokoúrovnovým. Má propracovaný pamětový model, a tak je to jeden z mála jazyků, který je pamětově bezpečný a zároveň nemá garbage collector.

Program se zkompiluje pomocí pomocného programu `cargo`, který je běžnou součástí jazyka. Funguje na stabilní verzi Rustu. Vybuildí se pomocí příkazu `cargo build --release` (to release je důležité kvůli optimalizacím, neoptimilizované programy jsou v rustu velmi pomalé).

Ukázkový výstup:
```
$ ./target/release/sat-solver wufs/wuf-A/wuf100-430-A1/wuf100-0238-A.mwcnf
425 -1 2 -3 4 5 6 -7 8 9 10 11 12 -13 -14 15 -16 17 -18 19 20 -21 -22 -23 -24 -25 -26 -27 -28 29 -30 31 32 -33 -34 -35 -36 -37 -38 39 -40 41 42 43 -44 45 46 47 -48 -49 -50 -51 52 -53 -54 -55 56 -57 58 59 -60 61 62 -63 64 -65 -66 -67 68 69 70 -71 72 73 74 75 -76 77 78 79 -80 81 82 -83 -84 85 86 87 -88 -89 -90 91 92 93 94 95 -96 97 -98 -99 -100 0
time: 4.5457ms
0.0045457
```

Architektura
------------

Základní architektura je CDCL řešič s efektivní implementací propagace, která je inspirována řešičem MiniSAT. Jednotlivé reprezentace nejsou tak vymazlené jako jsou MiniSAT, tak rychlostí se mu nejspíše ani neblížim. I přes inspiraci je podobnost v kódu velmi malá - celý zdrojový kód je nový.

Na základních (splnitelných) problémech ze stránky https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html funguje na velikosti cca. 200 proměných většinou do minuty (Počáteční implementace bez jakékoliv heuristiky).

Propagace
---------

Každá proměná má seznam klauzulí, ve kterých může svým přiřazením vytvořit konflikt. V rámci propagace se kontroluje jestli zbývá přiřadit poslední proměná nebo jestli už nevzniknul konflikt a podle toho se jedná. Složitost je lineární s počtem klauzulí ve kterých se proměná vyskytuje.

Účení nových klauzilí
---------------------

Bylo by pěkné moct se učit spoustu klauzulí a promazávat je, ale tenhle přístup je relativně náročný. Tak jsem zvolil, že budu mít poměrně přísný pravidla k naučení nové klauzule.

Aktuální pravidla jsou:

 - při příliš mnoha konfliktech se ani nesnaží učit
 - klauzule, která by měla víc než 5 literálů, tak se nenaučí
 - klauzule by měla být vyhodnotitelná z co nejvíce zafixovaných proměných
 - jednotlivý literály se zaměnují tak aby bylo možné dřív najít konflikt
 - např v $x_0 ∨ x_1 ∨ x_2$ a víme $¬x_2 ∨ x_3 ∨ x_4$ (to je ekvivalentní s $x_2 ⇒ x_3 ∨ x_4$), tak $x_2$ nahradíme a máme novou klauzuli $x_0 ∨ x_1 ∨ x_3 ∨ x_4$ (tohle opakuju dokud si myslím, že to má smysl)

Bylo by asi fajn ty parametry učení dát parametrizovatelný, nicméně aktuálně nejsou.

Pravidla jsou vybraný tak, aby se neučilo příliš hodně klauzulí a když už se nějaká naučí, tak aby měla přínos.

Selekční heuristika
-------------------

Heuristika která vybírá další proměné pro přiřazení bude hlavní věc, co se budu snažit ladit. Její implementace je nezávislá na solveru a je možné ji jednoduše nahrazovat.

Naivní vybírací heuristika - vybere první volnou proměnou co najde a tý přiřadí takovou hodnotu, aby způsobila co nejméně konfliktů. (Implementovaná pro nevážený SAT)

Hladová váhová heuristika - vybere proměnou s největší váhou jako true a takto postupuje. Pravděpodobně v průběhu způsobí konflikt a nějakou proměnou to prohodí v důsledku. Implementace je pomocí prioritní haldy, tedy složitost operací je $O(\ln n)$.

Hladová váhová heuristika s prořezáváním - postupuje stejně jak Hladová váhová heuristika, akorát počítá maximální dosažitelnou váhu a když je horší než už nalezená, tak provede ořez. (Implementovaná pro vážený SAT)

Hladová váhová heuristika s prořezáváním
----------------------------------------

Vlastně už tahle jednoduchá heuristika fungovala natolik dobře, že nejtěžší problémy z sady wuf-A nalezne nejlepší řešení řádově v milisekundách, tak není nutné vymýšlet lepší heuristiky. Ještě jsem ani nezačal ořezávavat agresivněji prostor, tak nalezené řešení je zaručeně nejlepší.

Výsledky
--------

Byla použita hladová váhová heuristika s prořezáváním.

Tabulka s deaktivovaným učením:

| sada               | průměrný čas | maximální čas |
|--------------------|------------:|------------:|
| `wuf20-78-N1`      |   $60,4 µs$ |  $128,1 µs$ |
| `wuf50-201-N1`     |  $307,9 µs$ |   $3,01 ms$ |
| `wuf75-310-N1`     |   $1,35 ms$ |   $5,29 ms$ |
| `wuf20-78-M1`      |   $61,2 µs$ |  $139,0 µs$ |
| `wuf50-201-M1`     |  $306,5 µs$ |   $2,34 ms$ |
| `wuf75-310-M1`     |   $1,34 ms$ |   $5,72 ms$ |
| `wuf20-78-Q1`      |  $108,9 µs$ |  $276,6 µs$ |
| `wuf50-201-Q1`     |   $2,35 ms$ |   $9,65 ms$ |
| `wuf75-310-Q1`     |   $27,6 ms$ |  $102,1 ms$ |
| `wuf20-78-R1`      |  $107,7 µs$ |  $346,9 µs$ |
| `wuf50-201-R1`     |   $2,37 ms$ |   $13,5 ms$ |
| `wuf75-310-R1`     |   $27,6 ms$ |  $105,7 ms$ |
| `wuf20-88-A1`      |   $72,5 µs$ |  $226,6 µs$ |
| `wuf20-91-A1`      |   $69,1 µs$ |  $198,1 µs$ |
| `wuf100-430-A1`    |   $8,31 ms$ |   $60,7 ms$ |

Tabulka s aktivovaným učením:

| sada               | průměrný čas | maximální čas |
|--------------------|------------:|------------:|
| `wuf20-78-N1`      |   $74.4 µs$ |  $140,4 µs$ |
| `wuf50-201-N1`     |  $329,0 µs$ |   $2,34 ms$ |
| `wuf75-310-N1`     |   $1,25 ms$ |   $4,78 ms$ |
| `wuf20-78-M1`      |   $77,8 µs$ |  $126,8 µs$ |
| `wuf50-201-M1`     |  $324,9 µs$ |   $2,46 ms$ |
| `wuf75-310-M1`     |   $1,29 ms$ |   $4,99 ms$ |
| `wuf20-78-Q1`      |  $128,9 µs$ |  $312,3 µs$ |
| `wuf50-201-Q1`     |   $2,22 ms$ |   $8,82 ms$ |
| `wuf75-310-Q1`     |   $24,8 ms$ |   $76,9 ms$ |
| `wuf20-78-R1`      |  $132,8 µs$ |  $333,5 µs$ |
| `wuf50-201-R1`     |   $2,27 ms$ |   $8,81 ms$ |
| `wuf75-310-R1`     |   $23,9 ms$ |   $74,7 ms$ |
| `wuf20-88-A1`      |   $83,4 µs$ |  $166,6 µs$ |
| `wuf20-91-A1`      |   $82,1 µs$ |  $137,4 µs$ |
| `wuf100-430-A1`    |   $7,20 ms$ |   $52,1 ms$ |

Během vyhodnocování jsem narazil na chybu v učení klauzulí - ta byla odstraněna. Tím najde můj řešič optimální řešení pro všechny zadané problémy s maximálním časem $76,9 ms$ (s deaktivovaným učením tento čas stoupne na $105,7 ms$).

Zkoušel jsem porovnávat dodané nalezené optimální řešení a mnou nalezené optimální řešení. Pro `wuf20-88-A1` a `wuf20-91-A1` jsem došel ke stejným výsledkům. Pro `wuf20-78-M1` taktéž. Pro `wuf50-201-M1` a `wuf50-201-Q1` těch daných řešení už moc není, ale na těch co jsou tak se shoduju. Na `wuf20-78-Q1` a `wuf20-78-N1` také shoda. Vzhledem k počtu shod je pravděpodobné, že moje implementace funguje správně.

Zkusil jsem spustit 10 nezkrácených problémů s 150 proměnými a 645 klauzulemi. Váhy jsem dal náhodné v rozmezí 100 až 1500 - bez ohledu na řešení. Dá očekávat, že to budou velmi těžké problémy.

| problém          |     čas    |
|------------------|-----------:|
| `wuf150-01`      |   $37,3 s$ |
| `wuf150-02`      |  $520,2 s$ |
| `wuf150-03`      |   $76,3 s$ |
| `wuf150-04`      |   $49,8 s$ |
| `wuf150-05`      |  $225,2 s$ |
| `wuf150-06`      |    $8,0 s$ |
| `wuf150-07`      |    $8,6 s$ |
| `wuf150-08`      |   $29,9 s$ |
| `wuf150-09`      |    $5,2 s$ |
| `wuf150-010`     |   $13,2 s$ |
| průměrný čas     |   $97,4 s$ |
| maximální čas    |  $520,2 s$ |

Výsledek je celkem přesvědčivý, akorát 2 instance byli těžší a ostatní řešič zvládl v desítkách sekund. Dá se předpokládat, že ty těžké instance měli malé řešení vzhledem k součtu vah a proto nutili řešič procházet mnohem víc prostoru.

Mnou nalezené optimální řešení jsou ve složce `optimal_solutions` spolu s extrémní sadou `wuf150`. Spouštěl jsem to pomocí skriptu `runner.py` na 4-6 jádrech najednou. Například celá sada `wuf-N1` trvá $7,6 s$ na 6 jádrech.

Testováno bylo na AMD 2700x s frekvencí 4,1 GHz.

Závěr
-----

Návaznost na zadané metody je taková, že naučené klauzule tvoří tabu, kam se řešič už nebude přístě koukat. Rychlost je taková, že je těžké na něm ladit jednotlivé nastavení. Zkusil jsem vypnout učení a výsledky jsou nepřesvědčivé v tom, jestli to vůbec pomáhá.

Je zde prostor pro vylepšení, například ořezávání je celkem naivní. Nicméně rychlost je tak velká, že mě to nepřijde nutné.

S výsledkem jsem spokojený, myslím že řešič může mít nějaké uptlatnění. Ikdyby to mělo být jen hledání optimálního řešení pro tento předmět.
