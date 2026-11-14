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
The machine is an Apple M2 with Java 25.0.2 and a heap of 4 GB.
The best throughput of each document is in bold, and so is every throughput within 5% of it: the runs of a measurement spread by 2% in the median, and by up to 4% in three quarters of the measurements.
The last row of each table is the heap allocated per byte of input, with the least in bold.
The total of nativejson-benchmark is the harness's, and that of json-benchmark and json-dummy-data is the size of all documents over the sum of their mean times.

## Results: `JsonGrammar`

### nativejson-benchmark

Throughput in MiB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 98 | **115** | 101 | 43 | 20 |
| `citm_catalog.json` | **188** | 115 | **185** | 72 | 35 |
| `twitter.json` | **166** | 108 | 144 | 74 | 38 |
| total | **128** | 114 | **128** | 54 | 25 |
| allocated, B per byte | **11.0** | 15.8 | 18.9 | 61.1 | 90.2 |

### json-benchmark

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 105 | **162** | 116 | 41 | 21 |
| `citm_catalog.json` | **200** | 129 | 144 | 87 | 36 |
| `twitter.json` | **180** | 126 | 147 | 87 | 40 |
| `verysmall.json` | 27 | **30** | 27 | 13 | 7.5 |
| `fgo.json` | **66** | 62 | 54 | 26 | 15 |
| `otfcc.json` | **45** | 42 | 36 | 17 | 9.7 |
| `poet.json` | 291 | 307 | **363** | 182 | 69 |
| `gsoc-2018.json` | 224 | 221 | **411** | 178 | 55 |
| total | **55** | 53 | 45 | 21 | 12 |
| allocated, B per byte | **21.4** | 48.9 | 44.1 | 164.1 | 219.4 |

### json-dummy-data

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `128KB-min.json` | 116 | **147** | 112 | 46 | 25 |
| `128KB.json` | 189 | 178 | **228** | 115 | 43 |
| `1MB-min.json` | 104 | **115** | 104 | 45 | 24 |
| `1MB.json` | 186 | 176 | **224** | 111 | 42 |
| `256KB-min.json` | 106 | **118** | 107 | 46 | 25 |
| `256KB.json` | 188 | 178 | **229** | 116 | 43 |
| `512KB-min.json` | 103 | **115** | 105 | 45 | 24 |
| `512KB.json` | 188 | 177 | **228** | 115 | 42 |
| `5MB-min.json` | 95 | **102** | 93 | 40 | 20 |
| `5MB.json` | 171 | 161 | **203** | 94 | 37 |
| `64KB-min.json` | 105 | **118** | 107 | 46 | 25 |
| `64KB.json` | 187 | 180 | **229** | 118 | 42 |
| total | 133 | 135 | **142** | 63 | 29 |
| allocated, B per byte | **7.9** | 18.0 | 20.2 | 57.0 | 76.0 |

### json-test-suite

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| 95 valid documents (y_) | 36 | **47** | 40 | 22 | 13 |
| allocated, B per byte | **50.4** | 84.0 | 92.4 | 201.7 | 285.7 |

## Results: fastparse's grammar

### nativejson-benchmark

Throughput in MiB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 58 | **66** | **64** | 33 | 17 |
| `citm_catalog.json` | **177** | 161 | **168** | 69 | 30 |
| `twitter.json` | **206** | 169 | **204** | 78 | 36 |
| total | 89 | **94** | **95** | 45 | 22 |
| allocated, B per byte | 14.9 | **14.7** | 15.3 | 71.5 | 101.3 |

### json-benchmark

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `canada.json` | 63 | **79** | 73 | 34 | 19 |
| `citm_catalog.json` | **212** | 188 | **205** | 86 | 31 |
| `twitter.json` | 225 | 227 | **258** | 95 | 38 |
| `verysmall.json` | 25 | **45** | 31 | 13 | 6.9 |
| `fgo.json` | 82 | **107** | 75 | 28 | 15 |
| `otfcc.json` | 56 | **70** | 50 | 19 | 10 |
| `poet.json` | 346 | 491 | **650** | 242 | 76 |
| `gsoc-2018.json` | 260 | 315 | **773** | 235 | 58 |
| total | 68 | **87** | 62 | 23 | 13 |
| allocated, B per byte | **18.3** | 18.4 | 20.1 | 163.3 | 224.2 |

### json-dummy-data

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| `128KB-min.json` | 138 | **216** | 184 | 46 | 26 |
| `128KB.json` | 208 | 267 | **435** | 123 | 44 |
| `1MB-min.json` | 127 | 168 | **179** | 46 | 25 |
| `1MB.json` | 205 | 267 | **421** | 119 | 43 |
| `256KB-min.json` | 129 | 170 | **182** | 47 | 26 |
| `256KB.json` | 207 | 266 | **434** | 124 | 44 |
| `512KB-min.json` | 128 | 169 | **180** | 47 | 26 |
| `512KB.json` | 207 | 268 | **433** | 124 | 43 |
| `5MB-min.json` | 122 | 156 | **172** | 42 | 22 |
| `5MB.json` | 201 | 258 | **388** | 105 | 40 |
| `64KB-min.json` | 129 | 170 | **181** | 48 | 26 |
| `64KB.json` | 207 | 265 | **429** | 125 | 43 |
| total | 161 | 208 | **263** | 68 | 31 |
| allocated, B per byte | **6.0** | **6.0** | 6.5 | 49.5 | 69.0 |

### json-test-suite

Throughput in MB/s.

| Document | Parrot | parboiled2 | fastparse | cats-parse | Parsley |
| --- | ---: | ---: | ---: | ---: | ---: |
| 95 valid documents (y_) | 50 | **73** | 63 | 23 | 13 |
| allocated, B per byte | **25.2** | 42.0 | 42.0 | 184.9 | 260.5 |

## Running

From this directory, with sbt:

```sh
sbt "runMain parrot.benchmarks.Verify"
sbt "runMain parrot.benchmarks.Compare [--grammar=fastparse] <library> [data set ...]"
```

The library is one of `Parrot`, `parboiled2`, `fastparse`, `cats-parse` and `Parsley`, and the data sets are `json-test-suite`, `json-dummy-data`, `json-benchmark` and `nativejson-benchmark`, all by default.
The measurements run in a JVM forked with the JDK that sbt runs on, which `sbt --java-home <JDK>` chooses.
The build compiles Parrot and its harness from the sources of the parent directory, so that the libraries compared stay out of Parrot's build.
