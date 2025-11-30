import tempfile
import os
import json
import importlib.util


def load_module_from_path(path):
    spec = importlib.util.spec_from_file_location("compare_logs", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_normalize_and_parse_line():
    # Load the compare_logs module directly from file
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
    cmp_path = os.path.join(repo_root, "script", "python", "makefile", "compare_logs.py")
    mod = load_module_from_path(cmp_path)

    # A well-formed commit log line (simplified)
    line = "core 0: 0x80000000 (0x00000013) some extra info"
    normalized = mod.normalize_line(line)
    assert normalized is not None
    pc, inst, rest, raw = normalized
    assert pc == 0x80000000
    assert inst == 0x00000013


def test_parse_log_file(tmp_path):
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
    cmp_path = os.path.join(repo_root, "script", "python", "makefile", "compare_logs.py")
    mod = load_module_from_path(cmp_path)

    # create a small fake rtl log with a couple of commit lines
    content = []
    content.append("core 0: 0x80000000 (0x00000013) nop\n")
    content.append("core 0: 0x80000004 (0x00000093) addi x1, x0, 0\n")

    p = tmp_path / "rtl.log"
    p.write_text(''.join(content))

    entries = mod.parse_log(str(p), skip_init=False, skip_csr=False)
    assert len(entries) == 2
    assert entries[0][0] == 0x80000000
    assert entries[1][1] == 0x00000093
