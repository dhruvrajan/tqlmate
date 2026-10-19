#!/usr/bin/env bash
# Build assembly JAR + GraalVM native-image binary for tqlmate-scala.
#
# Why GraalVM (not Scala Native): the official TypeDB 3.13.6 Java driver ships
# platform JNI natives (`libtypedb_driver_jni-*.so`). GraalVM can embed those as
# classpath resources that the driver's Loader unpacks at runtime. Scala Native
# cannot load the typedb-driver JNI artifacts.
#
# Gotcha: GraalVM native-image silently skips large DEFLATE-compressed `.so`
# entries inside the fat JAR. We therefore also ship an uncompressed
# (ZIP_STORED) companion jar containing the Linux x86_64 JNI library and put
# it on the native-image classpath.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
DIST="$ROOT/dist"
NI_CFG="$ROOT/native-image"
mkdir -p "$DIST"

SCALA_CLI="${SCALA_CLI:-scala-cli}"
if ! command -v "$SCALA_CLI" >/dev/null 2>&1; then
  if [[ -x /tmp/bins/scala-cli ]]; then
    SCALA_CLI=/tmp/bins/scala-cli
  else
    echo "scala-cli not found; install it or set SCALA_CLI" >&2
    exit 1
  fi
fi

if [[ -z "${JAVA_HOME:-}" || ! -x "${JAVA_HOME}/bin/native-image" ]]; then
  if [[ -x /tmp/bins/graalvm-community-openjdk-21.0.2+13.1/bin/native-image ]]; then
    JAVA_HOME=/tmp/bins/graalvm-community-openjdk-21.0.2+13.1
  fi
fi
if [[ -z "${JAVA_HOME:-}" || ! -x "${JAVA_HOME}/bin/native-image" ]]; then
  echo "GraalVM native-image not found; set JAVA_HOME to a GraalVM JDK 21+" >&2
  exit 1
fi
export JAVA_HOME
export PATH="${JAVA_HOME}/bin:${PATH}"

echo "==> Packaging assembly JAR"
"$SCALA_CLI" --power package \
  --scala 3.3.6 --jvm 21 \
  --dependency com.typedb:typedb-driver:3.13.6 \
  --repository https://repo.typedb.com/public/public-release/maven/ \
  --resource-dirs "$ROOT/resources" \
  --assembly \
  --main-class tqlmate.cli.Main \
  -o "$DIST/tqlmate-scala.jar" \
  --force \
  "$ROOT/cli" "$ROOT/verified/src" "$ROOT/runtime-shim"

echo "==> Building uncompressed JNI companion jar"
python3 - <<PY
import zipfile, tempfile, os
from pathlib import Path
jar = Path("$DIST/tqlmate-scala.jar")
out = Path("$DIST/typedb-jni-linux-x86_64.jar")
name = "libtypedb_driver_jni-linux-x86_64.so"
with zipfile.ZipFile(jar) as z, tempfile.TemporaryDirectory() as td:
    z.extract(name, td)
    so = Path(td) / name
    with zipfile.ZipFile(out, "w", compression=zipfile.ZIP_STORED) as w:
        w.write(so, arcname=name)
print(f"wrote {out} ({out.stat().st_size} bytes)")
PY

echo "==> Building native-image (GraalVM)"
native-image \
  -cp "$DIST/tqlmate-scala.jar:$DIST/typedb-jni-linux-x86_64.jar" \
  tqlmate.cli.Main \
  --no-fallback \
  -H:+ReportExceptionStackTraces \
  -H:+JNI \
  -H:ConfigurationFileDirectories="$NI_CFG" \
  --initialize-at-run-time=com.typedb,io.netty,ch.qos.logback,org.slf4j \
  -o "$DIST/tqlmate-scala" \
  2>&1 | tee "$DIST/native-image.log"

ls -lh "$DIST/tqlmate-scala" "$DIST/tqlmate-scala.jar" "$DIST/typedb-jni-linux-x86_64.jar"
echo "Native binary: $DIST/tqlmate-scala"
echo "Assembly JAR:  $DIST/tqlmate-scala.jar"
