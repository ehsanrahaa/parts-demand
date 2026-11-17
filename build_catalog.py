#!/usr/bin/env python3
"""کاتالوگ قطعه×خودرو را از بذر می‌سازد. یک‌بار اجرا و catalog.json کامیت می‌شود."""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
seed = json.load(open(os.path.join(HERE, "catalog_seed.json"), encoding="utf-8"))

combos = []
for p in seed["parts"]:
    hint = "، ".join(seed["brand_hints"].get(p["cat"], []))
    for v in seed["vehicles"]:
        combos.append({
            "id": f'{p["key"]}@{v["key"]}',
            "part": p["name"],
            "part_key": p["key"],
            "cat": p["cat"],
            "vehicle": v["name"],
            "vehicle_key": v["key"],
            "models": v["models"],
            "brand_hint": hint,
            "spec": f'{p["cat"]} | سازگار با {v["name"]} ({v["models"]})',
        })

out = {
    "parts": seed["parts"],
    "vehicles": seed["vehicles"],
    "brands": seed["brands"],
    "combos": combos,
}
json.dump(out, open(os.path.join(HERE, "catalog.json"), "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print(f'{len(seed["parts"])} قطعه × {len(seed["vehicles"])} خودرو = {len(combos)} ترکیب')
