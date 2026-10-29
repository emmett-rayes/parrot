from pathlib import Path
import pants.backend.scala.dependency_inference.scala_parser as scala_parser
import pants.util.resources as pants_resources

# Save the original read_resource function reference
_original_read_resource = pants_resources.read_resource

def patched_read_resource(package: str, name: str) -> bytes:
    # Intercept specifically when Pants goes to look up ScalaParser.scala
    if package == "pants.backend.scala.dependency_inference" and name == "ScalaParser.scala":
        override_path = Path(__file__).parent / "ScalaParser.scala"
        if override_path.is_file():
            return override_path.read_bytes()
            
    # Fall back to default behavior for all other internal resources
    return _original_read_resource(package, name)

# Overwrite references in both the source module and the consuming module
pants_resources.read_resource = patched_read_resource
scala_parser.read_resource = patched_read_resource

def rules():
    # We don't need new rules; the monkeypatch handles the swap transparently
    return []
