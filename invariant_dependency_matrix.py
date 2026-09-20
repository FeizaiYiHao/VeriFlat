#!/usr/bin/env python3
"""Report KernelK invariant leaves, their field dependencies, and helper coverage."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent
KERNEL_SPEC = ROOT / "src/kernel/kernel_k_define_spec.rs"
KERNEL_DIR = ROOT / "src/kernel"

KERNEL_FIELDS = {
    "pt_mp", "it_mp", "irt", "pg_arr", "cpu_arr", "pcid_needflush",
    "cpu_published", "ctn_mp", "sched_mp", "pcid_allc_mp", "cpu_set_mp",
    "prc_mp", "thr_mp", "ep_mp", "allc_4k_mp", "allc_2m_mp",
    "allc_1g_mp", "cpu_tlb", "iommu_tlb", "rt_ctn", "dflt_pt",
}


def leaf(
    group: str,
    name: str,
    marker: str,
    *fields: str,
    helper_targets: tuple[str, ...] | None = None,
):
    return {
        "group": group,
        "leaf": name,
        "marker": marker,
        "fields": fields,
        "helper_targets": helper_targets or (name,),
    }


MATRIX = [
    leaf("subsystems", "default_pagetable_wf", "self.default_pagetable_wf()", "dflt_pt", "pt_mp"),
    leaf("subsystems", "pagetable_perms_wf", "pagetable_perms_wf(self.pt_mp)", "pt_mp"),
    leaf("subsystems", "iommu_table_perms_wf", "iommu_table_perms_wf(self.it_mp)", "it_mp"),
    leaf("subsystems", "iommu_root_table_wf", "self.irt.wf()", "irt"),
    leaf("subsystems", "page_array_wf", "page_array_wf(self.pg_arr)", "pg_arr"),
    leaf("subsystems", "cpu_array_wf", "cpu_array_wf(self.cpu_arr", "cpu_arr", "dflt_pt"),
    leaf("subsystems", "pcid_needflush_wf", "pcid_needflush_wf(self.pcid_needflush)", "pcid_needflush"),
    leaf("subsystems", "cpu_published_wf", "cpu_published_wf(self.cpu_published", "cpu_published", "cpu_arr", "pcid_needflush"),
    leaf("subsystems", "cpu_tlb_inv", "self.cpu_tlb.inv()", "cpu_tlb"),
    leaf("subsystems", "iommu_tlb_inv", "self.iommu_tlb.inv()", "iommu_tlb"),
    leaf("subsystems", "container_perms_wf", "container_perms_wf(self.ctn_mp)", "ctn_mp"),
    leaf("subsystems", "process_perms_wf", "process_perms_wf(self.prc_mp)", "prc_mp"),
    leaf("subsystems", "thread_perms_wf", "thread_perms_wf(self.thr_mp)", "thr_mp"),
    leaf("subsystems", "scheduler_perms_wf", "scheduler_perms_wf(self.sched_mp)", "sched_mp"),
    leaf("subsystems", "cpu_set_perms_wf", "cpu_set_perms_wf(self.cpu_set_mp)", "cpu_set_mp"),
    leaf("subsystems", "pcid_allocator_perms_wf", "pcid_allocator_perms_wf(self.pcid_allc_mp)", "pcid_allc_mp"),
    leaf("subsystems", "endpoint_perms_wf", "endpoint_perms_wf(self.ep_mp)", "ep_mp"),
    leaf("subsystems", "allocator_perms_wf_4k", "allocator_perms_wf(self.allc_4k_mp)", "allc_4k_mp", helper_targets=("allocator_perms_wf",)),
    leaf("subsystems", "allocator_perms_wf_2m", "allocator_perms_wf(self.allc_2m_mp)", "allc_2m_mp", helper_targets=("allocator_perms_wf",)),
    leaf("subsystems", "allocator_perms_wf_1g", "allocator_perms_wf(self.allc_1g_mp)", "allc_1g_mp", helper_targets=("allocator_perms_wf",)),

    leaf(
        "memory",
        "allocator_pages_wf",
        "allocator_pages_wf(self.pg_arr",
        "pg_arr",
        "allc_4k_mp",
        "allc_2m_mp",
        "allc_1g_mp",
        helper_targets=(
            "allocator_pages_wf",
            "allocator_4k_pages_wf",
            "allocator_2m_pages_wf",
            "allocator_1g_pages_wf",
        ),
    ),
    leaf("memory", "container_page_owner_wf", "container_page_owner_wf(self.ctn_mp", "ctn_mp", "pg_arr"),
    leaf("memory", "hugepage_2m_wf", "hugepage_2m_wf(self.pg_arr)", "pg_arr"),
    leaf("memory", "hugepage_1g_wf", "hugepage_1g_wf(self.pg_arr)", "pg_arr"),
    leaf("memory", "page_pagetable_wf", "page_pagetable_wf(self.pt_mp", "pt_mp", "pg_arr"),
    leaf("memory", "container_process_page_pagetable_wf", "container_process_page_pagetable_wf(self.ctn_mp", "ctn_mp", "prc_mp", "pt_mp", "pg_arr"),
    leaf("memory", "container_pages_wf", "container_pages_wf(self.pg_arr", "pg_arr", "ctn_mp"),
    leaf("memory", "process_pages_wf", "process_pages_wf(self.pg_arr", "pg_arr", "prc_mp"),
    leaf("memory", "pagetable_pages_wf", "pagetable_pages_wf(self.pt_mp", "pt_mp", "pg_arr"),
    leaf("memory", "iommu_table_pages_wf", "iommu_table_pages_wf(self.it_mp", "it_mp", "pg_arr"),
    leaf("memory", "thread_pages_wf", "thread_pages_wf(self.thr_mp", "thr_mp", "pg_arr"),
    leaf("memory", "scheduler_pages_wf", "scheduler_pages_wf(self.sched_mp", "sched_mp", "pg_arr"),
    leaf("memory", "cpu_set_pages_wf", "cpu_set_pages_wf(self.cpu_set_mp", "cpu_set_mp", "pg_arr"),
    leaf("memory", "pcid_allocator_pages_wf", "pcid_allocator_pages_wf(", "pg_arr", "pcid_allc_mp"),
    leaf(
        "memory",
        "thread_staged_pages_wf",
        "thread_staged_pages_wf(self.thr_mp",
        "thr_mp",
        "pg_arr",
        helper_targets=(
            "thread_staged_pages_wf",
            "thread_staged_pages_4k_wf",
            "thread_staged_pages_2m_wf",
            "thread_staged_pages_1g_wf",
        ),
    ),
    leaf("memory", "endpoint_pages_wf", "endpoint_pages_wf(self.ep_mp", "ep_mp", "pg_arr"),
    leaf("memory", "process_pagetable_match", "process_pagetable_match(self.prc_mp", "prc_mp", "pt_mp"),
    leaf("memory", "process_iommu_table_match", "process_iommu_table_match(self.prc_mp", "prc_mp", "it_mp"),
    leaf(
        "memory",
        "allocator_free_pages_wf",
        "self.allocator_free_pages_wf()",
        "allc_4k_mp",
        "allc_2m_mp",
        "allc_1g_mp",
        helper_targets=("allocator_free_page_ptrs_wf",),
    ),
    leaf(
        "memory",
        "container_process_allocator_quota_wf",
        "container_process_allocator_quota_wf(self.ctn_mp",
        "ctn_mp",
        "prc_mp",
        "thr_mp",
        "allc_4k_mp",
        "allc_2m_mp",
        "allc_1g_mp",
        helper_targets=(
            "container_process_allocator_quota_wf",
            "container_process_allocator_quota_4k_wf",
            "container_process_allocator_quota_2m_wf",
            "container_process_allocator_quota_1g_wf",
        ),
    ),
    leaf("memory", "container_allocator_wf", "container_allocator_wf(self.ctn_mp", "ctn_mp", "allc_4k_mp", "allc_2m_mp", "allc_1g_mp"),
    leaf("memory", "container_allocator_free_4k_page_wf", "container_allocator_free_4k_page_wf(self.allc_4k_mp", "allc_4k_mp", "pg_arr"),
    leaf("memory", "container_allocator_free_2m_page_wf", "container_allocator_free_2m_page_wf(self.allc_2m_mp", "allc_2m_mp", "pg_arr"),
    leaf("memory", "container_allocator_free_1g_page_wf", "container_allocator_free_1g_page_wf(self.allc_1g_mp", "allc_1g_mp", "pg_arr"),

    leaf("process", "container_tree_wf", "container_tree_wf(self.rt_ctn", "rt_ctn", "ctn_mp"),
    leaf("process", "root_process_in_processes", "root_process_in_processes()", "rt_ctn", "ctn_mp"),
    leaf("process", "container_process_wf", "container_process_wf(self.ctn_mp", "ctn_mp", "prc_mp"),
    leaf("process", "per_container_process_tree_wf", "per_container_process_tree_wf(self.ctn_mp", "ctn_mp", "prc_mp"),
    leaf("process", "container_endpoint_wf", "container_endpoint_wf(self.ctn_mp", "ctn_mp", "ep_mp"),
    leaf("process", "container_cpu_wf", "container_cpu_wf(self.ctn_mp", "ctn_mp", "cpu_set_mp", "cpu_arr"),
    leaf("process", "thread_endpoint_ref_counter_wf", "thread_endpoint_ref_counter_wf(self.thr_mp", "thr_mp", "ep_mp"),
    leaf("process", "thread_endpoint_queue_wf", "thread_endpoint_queue_wf(self.thr_mp", "thr_mp", "ep_mp"),
    leaf("process", "thread_caller_callee_wf", "thread_caller_callee_wf(self.thr_mp)", "thr_mp"),
    leaf("process", "container_thread_endpoint_wf", "container_thread_endpoint_wf(self.ctn_mp", "ctn_mp", "thr_mp", "ep_mp"),
    leaf("process", "container_scheduler_wf", "container_scheduler_wf(self.ctn_mp", "ctn_mp", "sched_mp"),
    leaf("process", "container_cpu_set_wf", "container_cpu_set_wf(self.ctn_mp", "ctn_mp", "cpu_set_mp"),
    leaf("process", "container_pcid_allocator_wf", "container_pcid_allocator_wf(", "ctn_mp", "pcid_allc_mp"),
    leaf("process", "process_pcid_allocator_wf", "process_pcid_allocator_wf(", "ctn_mp", "prc_mp", "pcid_allc_mp"),
    leaf("process", "container_thread_scheduler_wf", "container_thread_scheduler_wf(self.ctn_mp", "ctn_mp", "thr_mp", "sched_mp"),
    leaf("process", "container_thread_wf", "container_thread_wf(self.ctn_mp", "ctn_mp", "thr_mp"),
    leaf("process", "process_cpu_wf", "process_cpu_wf(self.prc_mp", "prc_mp", "cpu_arr"),
    leaf("process", "process_thread_wf", "process_thread_wf(self.prc_mp", "prc_mp", "thr_mp"),
    leaf("process", "thread_cpu_wf", "thread_cpu_wf(self.thr_mp", "thr_mp", "cpu_arr"),

    leaf("kernel", "iommu_root_table_process_wf", "iommu_root_table_process_wf(", "irt", "prc_mp", "it_mp"),
    leaf("kernel", "process_pci_function_ownership_wf", "process_pci_function_ownership_wf(", "irt", "prc_mp"),
    leaf("kernel", "iommu_tlb_wf_spec", "iommu_tlb_wf_spec(", "iommu_tlb", "irt", "prc_mp", "it_mp"),
    leaf("kernel", "cpu_dirty_map_wf", "cpu_dirty_map_wf(self.ctn_mp", "ctn_mp", "cpu_set_mp", "prc_mp", "cpu_arr", "cpu_tlb", "pt_mp", "pcid_needflush"),
    leaf("kernel", "tlb_wf_spec", "tlb_wf_spec(self.cpu_tlb", "cpu_tlb", "pt_mp", "cpu_arr", "pcid_needflush"),
]

GROUP_FUNCTIONS = {
    "subsystems": ("subsystems_inv", 0),
    "memory": ("memory_management_inv", 0),
    "process": ("process_management_inv", 0),
    "kernel": ("inv", 3),
}

AGGREGATE_HELPER_TARGETS = {
    "memory_management_inv": "memory",
    "process_management_inv": "process",
}

RELATION_HELPER_TARGETS = {
    "cpu_lock_id": "typed-lock-map alignment",
    "endpoint_lock_id": "typed-lock-map alignment",
    "process_lock_id": "typed-lock-map alignment",
    "thread_lock_id": "typed-lock-map alignment",
}


def function_body(source: str, name: str) -> str:
    match = re.search(rf"\bpub open spec fn {re.escape(name)}\b", source)
    if not match:
        raise ValueError(f"missing spec function {name}")
    start = source.find("{", match.end())
    depth = 0
    for index in range(start, len(source)):
        if source[index] == "{":
            depth += 1
        elif source[index] == "}":
            depth -= 1
            if depth == 0:
                return source[start:index + 1]
    raise ValueError(f"unterminated spec function {name}")


def helper_target(name: str) -> str:
    target = name.split("_preserved_for", 1)[0]
    return target.removeprefix("lemma_")


def proof_helpers() -> list[str]:
    pattern = re.compile(r"\b(?:pub\s+)?proof fn ([A-Za-z0-9_]+)")
    helpers = set()
    for path in sorted(KERNEL_DIR.rglob("*.rs")):
        for name in pattern.findall(path.read_text()):
            if "preserved_for" in name or "no_change_imply" in name:
                helpers.add(name)
    return sorted(helpers)


def matrix_rows():
    helpers = proof_helpers()
    rows = []
    for entry in MATRIX:
        matches = sorted(
            name for name in helpers
            if helper_target(name) in entry["helper_targets"]
        )
        rows.append({**entry, "fields": list(entry["fields"]), "helpers": matches})
    aggregate_helpers = {
        target: sorted(name for name in helpers if helper_target(name) == target)
        for target in AGGREGATE_HELPER_TARGETS
    }
    relation_helpers = {
        target: sorted(name for name in helpers if helper_target(name) == target)
        for target in RELATION_HELPER_TARGETS
    }
    return rows, helpers, aggregate_helpers, relation_helpers


def validate(rows, helpers, aggregate_helpers, relation_helpers) -> list[str]:
    errors = []
    source = KERNEL_SPEC.read_text()
    names = [row["leaf"] for row in rows]
    if len(names) != len(set(names)):
        errors.append("duplicate invariant leaf names")
    for row in rows:
        unknown = set(row["fields"]) - KERNEL_FIELDS
        if unknown:
            errors.append(f"{row['leaf']}: unknown fields {sorted(unknown)}")
    for group, (function, extra_conjuncts) in GROUP_FUNCTIONS.items():
        body = function_body(source, function)
        group_rows = [row for row in rows if row["group"] == group]
        actual = len(re.findall(r"(?m)^\s*&&&", body))
        expected = len(group_rows) + extra_conjuncts
        if actual != expected:
            errors.append(f"{function}: {actual} top-level conjuncts, matrix expects {expected}")
        for row in group_rows:
            if row["marker"] not in body:
                errors.append(f"{function}: missing marker for {row['leaf']}: {row['marker']}")
    classified = {
        name
        for row in rows
        for name in row["helpers"]
    }
    classified.update(
        name
        for names in aggregate_helpers.values()
        for name in names
    )
    classified.update(
        name
        for names in relation_helpers.values()
        for name in names
    )
    unclassified = sorted(set(helpers) - classified)
    if unclassified:
        errors.append(f"unclassified preservation helpers: {', '.join(unclassified)}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="validate the matrix against live KernelK specs")
    parser.add_argument("--json", action="store_true", help="emit machine-readable rows")
    parser.add_argument("--show-helpers", action="store_true", help="include matching helper names")
    args = parser.parse_args()

    rows, helpers, aggregate_helpers, relation_helpers = matrix_rows()
    errors = validate(rows, helpers, aggregate_helpers, relation_helpers)
    leaf_helpers = {name for row in rows for name in row["helpers"]}
    aggregate_helper_names = {
        name for names in aggregate_helpers.values() for name in names
    }
    relation_helper_names = {
        name for names in relation_helpers.values() for name in names
    }
    classified = leaf_helpers | aggregate_helper_names | relation_helper_names
    if args.json:
        print(json.dumps({
            "rows": rows,
            "helper-count": len(helpers),
            "leaf-helper-count": len(leaf_helpers),
            "aggregate-helpers": aggregate_helpers,
            "relation-helpers": relation_helpers,
            "classified-helper-count": len(classified),
            "unclassified-helpers": sorted(set(helpers) - classified),
            "errors": errors,
        }, indent=2))
    elif args.check:
        if errors:
            for error in errors:
                print(error, file=sys.stderr)
        print(
            f"{len(rows)} invariant leaves; {len(helpers)} preservation helpers "
            f"({len(leaf_helpers)} leaf, {len(aggregate_helper_names)} aggregate, "
            f"{len(relation_helper_names)} relation); {len(classified)} classified"
        )
    else:
        helper_column = " | helpers" if args.show_helpers else ""
        print(f"group | leaf | KernelK fields | helper count{helper_column}")
        print("--- | --- | --- | ---:" + (" | ---" if args.show_helpers else ""))
        for row in rows:
            values = f"{row['group']} | {row['leaf']} | {', '.join(row['fields'])} | {len(row['helpers'])}"
            if args.show_helpers:
                values += " | " + ", ".join(row["helpers"])
            print(values)
        print(
            f"\n{len(rows)} leaves; {len(helpers)} preservation helpers "
            f"({len(leaf_helpers)} leaf, {len(aggregate_helper_names)} aggregate, "
            f"{len(relation_helper_names)} relation); {len(classified)} classified"
        )
        if errors:
            print("\nMatrix validation errors:", file=sys.stderr)
            for error in errors:
                print(f"- {error}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
