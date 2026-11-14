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

Each library runs each data set in its own JVM, after 30 warm-up runs per document (passes for JSONTestSuite, and 5 runs for json-benchmark), with trials that repeat a parse for at least 500 ms.
The machine is an Apple M2 with Java 21.0.11 and a heap of 4 GB.
The best throughput of each document is in bold, and so is every throughput within 5% of it: the runs of a measurement spread by 3% in the median, and by up to 5% in three quarters of the measurements.
The last row of each table is the heap allocated per byte of input, with the least in bold.
The total of nativejson-benchmark is the harness's, and that of json-benchmark and json-dummy-data is the size of all documents over the sum of their mean times.

## Results: `JsonGrammar`

### nativejson-benchmark

Throughput in MiB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | **95** | **95** | **91** | 44 | 19 |
| `citm_catalog.json` | **195** | 113 | **186** | 74 | 33 |
| `twitter.json` | **169** | 114 | 151 | 79 | 37 |
| total | **127** | 104 | **121** | 56 | 24 |
| allocated, B per byte | **11.0** | 20.9 | 18.5 | 61.1 | 90.2 |

### json-benchmark

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 92 | **123** | 91 | 39 | 20 |
| `citm_catalog.json` | **184** | 125 | 132 | 97 | 35 |
| `twitter.json` | **178** | 133 | 151 | 93 | 38 |
| `verysmall.json` | 22 | **28** | 8.7 | 13 | 6.0 |
| `fgo.json` | **67** | 63 | 54 | 26 | 13 |
| `otfcc.json` | **45** | 42 | 34 | 18 | 9.5 |
| `poet.json` | 289 | 298 | **372** | 182 | 68 |
| `gsoc-2018.json` | 227 | 231 | **426** | 176 | 55 |
| total | **56** | 53 | 44 | 22 | 12 |
| allocated, B per byte | **21.4** | 49.2 | 41.3 | 164.1 | 219.4 |

### json-dummy-data

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `128KB-min.json` | **106** | 99 | 97 | 41 | 23 |
| `128KB.json` | 192 | 181 | **222** | 119 | 42 |
| `1MB-min.json` | 102 | **123** | 94 | 46 | 22 |
| `1MB.json` | 198 | 176 | **232** | 116 | 41 |
| `256KB-min.json` | 105 | **123** | 99 | 49 | 23 |
| `256KB.json` | 198 | 178 | **234** | 120 | 40 |
| `512KB-min.json` | 102 | **122** | 99 | 46 | 23 |
| `512KB.json` | 198 | 178 | **238** | 120 | 42 |
| `5MB-min.json` | 94 | **107** | 85 | 41 | 20 |
| `5MB.json` | 184 | 162 | **212** | 102 | 37 |
| `64KB-min.json` | 105 | **123** | 101 | 49 | 24 |
| `64KB.json` | 198 | 179 | **237** | 122 | 42 |
| total | **136** | **138** | **137** | 66 | 28 |
| allocated, B per byte | **7.9** | 18.0 | 20.0 | 57.0 | 76.0 |

### json-test-suite

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| 95 valid documents (y_) | **27** | 14 | 8.5 | 9.3 | 7.0 |
| allocated, B per byte | **42.0** | 109.2 | 109.2 | 201.7 | 302.5 |

## Results: fastparse's grammar

### nativejson-benchmark

Throughput in MiB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 58 | **65** | **63** | 32 | 16 |
| `citm_catalog.json` | **187** | 164 | 168 | 71 | 29 |
| `twitter.json` | 186 | 177 | **202** | 80 | 35 |
| total | 89 | **95** | **93** | 45 | 21 |
| allocated, B per byte | 16.4 | **15.3** | 15.7 | 71.9 | 101.8 |

### json-benchmark

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 61 | **81** | 64 | 31 | 18 |
| `citm_catalog.json` | **201** | 184 | **193** | 86 | 30 |
| `twitter.json` | 190 | 222 | **250** | 94 | 37 |
| `verysmall.json` | 23 | **32** | 12 | 9.9 | 5.6 |
| `fgo.json` | 70 | **108** | 82 | 29 | 14 |
| `otfcc.json` | 49 | **71** | 55 | 19 | 9.5 |
| `poet.json` | 295 | 449 | **683** | 235 | 70 |
| `gsoc-2018.json` | 240 | 310 | **775** | 219 | 57 |
| total | 59 | **87** | 68 | 24 | 12 |
| allocated, B per byte | 25.0 | **18.9** | **18.9** | 163.5 | 224.4 |

### json-dummy-data

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `128KB-min.json` | 108 | 149 | **161** | 40 | 24 |
| `128KB.json` | 174 | **253** | 218 | 126 | 43 |
| `1MB-min.json` | 103 | **172** | 153 | 49 | 24 |
| `1MB.json` | 178 | **261** | 222 | 125 | 43 |
| `256KB-min.json` | 103 | **177** | 158 | 50 | 25 |
| `256KB.json` | 178 | **262** | 227 | 130 | 43 |
| `512KB-min.json` | 104 | **176** | 157 | 50 | 24 |
| `512KB.json` | 180 | **262** | 225 | 127 | 43 |
| `5MB-min.json` | 99 | **165** | 148 | 42 | 22 |
| `5MB.json` | 174 | **253** | 215 | 110 | 38 |
| `64KB-min.json` | 103 | **177** | 156 | 50 | 26 |
| `64KB.json` | 180 | **261** | 223 | 130 | 43 |
| total | 134 | **210** | 184 | 69 | 30 |
| allocated, B per byte | 10.4 | **6.1** | 6.3 | 49.5 | 69.0 |

### json-test-suite

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| 95 valid documents (y_) | **30** | 14 | 9.6 | 7.7 | 5.6 |
| allocated, B per byte | **33.6** | 50.4 | 58.8 | 184.9 | 268.9 |

## Running

From this directory, with sbt:

```sh
sbt "runMain parrot.benchmarks.Verify"
sbt "runMain parrot.benchmarks.Compare [--grammar=fastparse] <library> [data set ...]"
```

The library is one of `Parrot`, `parboiled2`, `fastparse`, `cats-parse` and `Parsley`, and the data sets are `json-test-suite`, `json-dummy-data`, `json-benchmark` and `nativejson-benchmark`, all by default.
The build compiles Parrot and its harness from the sources of the parent directory, so that the libraries compared stay out of Parrot's build.
