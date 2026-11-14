# Benchmarks

Parrot compared with [parboiled2](https://github.com/sirthias/parboiled2) 2.5.1, [fastparse](https://github.com/com-lihaoyi/fastparse) 3.1.1, [cats-parse](https://github.com/typelevel/cats-parse) 1.1.0 and [Parsley](https://github.com/j-mie6/parsley) 4.6.2 on JSON, with two grammars, each ported to every library:

- **`JsonGrammar`**, Parrot's JSON grammar ([`JsonGrammar.scala`](../src/main/scala/parrot/json/JsonGrammar.scala)), ported rule by rule in the files `*Json.scala`.
  Every port builds Parrot's syntax tree, up to the types of its collections and tuples.
- **fastparse's JSON grammar**, as [fastparse's documentation](https://com-lihaoyi.github.io/fastparse/) writes it in its section Json ([`FastparseJs.scala`](src/main/scala/parrot/benchmarks/FastparseJs.scala)), ported in the files `*Js.scala`.
  Every port builds its syntax tree `Js`.
  It is fastparse's example, not strict JSON: it takes no tab as whitespace, allows a leading `+` and control characters in strings, and keeps the escapes of a string undecoded.

Where a library's choice commits once an alternative has consumed input, as in cats-parse and Parsley, its ports `backtrack` or are `atomic` where the original grammar backtracks.
fastparse's `.!`, which returns the input a parser consumed, is `capture` in Parrot and parboiled2, `string` in cats-parse and `span` in Parsley.

## Correctness

`Verify` checks that every port accepts what the grammar's reference accepts, Parrot for `JsonGrammar` and fastparse for its own grammar, and builds the same tree.
It checks the 34 documents of nativejson-benchmark's Parse Validation and the 118 documents measured here, all of which both references accept.
On the Parse Validation, Parrot is right on 34 documents and fastparse's grammar on 31.

## Method

The documents are the valid ones of Parrot's JSON test sets, in [`src/test/resources/json`](../src/test/resources/json), measured by Parrot's own harness, [`JsonBenchmark`](../src/test/scala/parrot/json/JsonBenchmark.scala), with the methodology of each data set:

| Data set | Documents | Measure |
| --- | --- | --- |
| [nativejson-benchmark](https://github.com/miloyip/nativejson-benchmark) | its Parse documents, 0.6 to 2.3 MB | minimum of 10 trials, in MiB/s |
| [json-benchmark](https://github.com/TkTech/json_benchmark) | 8 documents, 7 B to 66 MB | mean of 5 loads, in MB/s |
| [json-dummy-data](https://microsoftedge.github.io/Demos/json-dummy-data/) | 12 documents, 43 kB to 5 MB, minified and indented | mean of 7 loads, in MB/s |
| [JSONTestSuite](https://github.com/nst/JSONTestSuite) | its 95 valid documents (`y_`), 1.2 kB in all | median of 7 passes over them, in MB/s |

Each library runs each data set in its own JVM, after a warm-up of at least 2 s per document (of passes over the documents for JSONTestSuite), with trials that repeat a parse for at least 500 ms.
The machine is an Apple M2 with Java 21.0.11 and a heap of 4 GB.
The best throughput of each document is in bold, and so is every throughput within 5% of it: the runs of a measurement spread by 2% in the median, and by up to 5% in nine tenths of the measurements.
The last row of each table is the heap allocated per byte of input, with the least in bold.
The total of nativejson-benchmark is the harness's, and that of json-benchmark and json-dummy-data is the size of all documents over the sum of their mean times.

## Results: `JsonGrammar`

### nativejson-benchmark

Throughput in MiB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 96 | **101** | **104** | 44 | 19 |
| `citm_catalog.json` | **194** | 114 | 184 | 75 | 33 |
| `twitter.json` | 170 | 115 | **189** | 79 | 37 |
| total | **128** | 108 | **134** | 56 | 25 |
| allocated, B per byte | **11.0** | 20.9 | 17.9 | 61.1 | 90.2 |

### json-benchmark

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 103 | **149** | 113 | 44 | 20 |
| `citm_catalog.json` | **197** | 130 | 144 | 88 | 35 |
| `twitter.json` | **180** | 137 | 160 | 92 | 38 |
| `verysmall.json` | 28 | **34** | 29 | 14 | 6.9 |
| `fgo.json` | **66** | **65** | 55 | 27 | 14 |
| `otfcc.json` | **45** | **45** | 36 | 18 | 9.3 |
| `poet.json` | 293 | 309 | **390** | 205 | 71 |
| `gsoc-2018.json` | 230 | 232 | **444** | 180 | 56 |
| total | **56** | **56** | 45 | 23 | 12 |
| allocated, B per byte | **21.4** | 49.2 | 41.3 | 164.1 | 219.4 |

### json-dummy-data

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `128KB-min.json` | **121** | 108 | 109 | 48 | 24 |
| `128KB.json` | 198 | 182 | **219** | 119 | 42 |
| `1MB-min.json` | 102 | **123** | 99 | 47 | 23 |
| `1MB.json` | 197 | 178 | **216** | 116 | 40 |
| `256KB-min.json` | 105 | **124** | 102 | 48 | 24 |
| `256KB.json` | 198 | 181 | **221** | 119 | 42 |
| `512KB-min.json` | 102 | **123** | 101 | 47 | 23 |
| `512KB.json` | 197 | 180 | **219** | 119 | 41 |
| `5MB-min.json` | 93 | **112** | 89 | 41 | 20 |
| `5MB.json` | 184 | 168 | **203** | 105 | 36 |
| `64KB-min.json` | 105 | **124** | 102 | 49 | 24 |
| `64KB.json` | 198 | 182 | **224** | 122 | 40 |
| total | **135** | **143** | **138** | 67 | 28 |
| allocated, B per byte | **7.9** | 18.0 | 20.0 | 57.0 | 76.0 |

### json-test-suite

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| 95 valid documents (y_) | 37 | **41** | **43** | 22 | 12 |
| allocated, B per byte | **50.4** | 84.0 | 84.0 | 201.7 | 285.7 |

## Results: fastparse's grammar

### nativejson-benchmark

Throughput in MiB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 58 | **64** | **64** | 33 | 16 |
| `citm_catalog.json` | **212** | 163 | 175 | 71 | 28 |
| `twitter.json` | **210** | 174 | **207** | 80 | 34 |
| total | **93** | **94** | **96** | 46 | 21 |
| allocated, B per byte | 15.4 | **15.3** | 15.5 | 71.9 | 101.8 |

### json-benchmark

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 63 | **81** | 70 | 34 | 18 |
| `citm_catalog.json` | **226** | 190 | 212 | 87 | 31 |
| `twitter.json` | 231 | 217 | **268** | 97 | 37 |
| `verysmall.json` | 28 | **36** | 31 | 13 | 6.5 |
| `fgo.json` | 85 | **100** | 81 | 28 | 14 |
| `otfcc.json` | 60 | **68** | 55 | 19 | 10 |
| `poet.json` | 346 | 444 | **684** | 241 | 74 |
| `gsoc-2018.json` | 258 | 303 | **775** | 224 | 57 |
| total | 72 | **83** | 68 | 24 | 12 |
| allocated, B per byte | **18.4** | 18.9 | 18.7 | 163.5 | 224.4 |

### json-dummy-data

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `128KB-min.json` | 137 | **162** | **170** | 48 | 26 |
| `128KB.json` | 203 | 266 | **413** | 128 | 43 |
| `1MB-min.json` | 130 | **175** | **171** | 48 | 24 |
| `1MB.json` | 201 | 266 | **405** | 125 | 43 |
| `256KB-min.json` | 130 | **179** | **174** | 50 | 25 |
| `256KB.json` | 203 | 267 | **413** | 129 | 43 |
| `512KB-min.json` | 132 | **177** | **169** | 49 | 25 |
| `512KB.json` | 202 | 266 | **411** | 129 | 42 |
| `5MB-min.json` | 126 | **163** | **164** | 43 | 22 |
| `5MB.json` | 198 | 256 | **383** | 114 | 39 |
| `64KB-min.json` | 131 | **177** | **173** | 50 | 25 |
| `64KB.json` | 202 | 267 | **406** | 130 | 42 |
| total | 162 | 211 | **252** | 71 | 30 |
| allocated, B per byte | **6.1** | **6.1** | 6.3 | 49.5 | 69.0 |

### json-test-suite

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| 95 valid documents (y_) | 51 | **69** | 62 | 22 | 12 |
| allocated, B per byte | **25.2** | 42.0 | 42.0 | 184.9 | 260.5 |

## Running

From this directory, with sbt:

```sh
sbt "runMain parrot.benchmarks.Verify"
sbt "runMain parrot.benchmarks.Compare [--grammar=fastparse] <library> [data set ...]"
```

The library is one of `Parrot`, `parboiled2`, `fastparse`, `cats-parse` and `Parsley`, and the data sets are `json-test-suite`, `json-dummy-data`, `json-benchmark` and `nativejson-benchmark`, all by default.
The build compiles Parrot and its harness from the sources of the parent directory, so that the libraries compared stay out of Parrot's build.
