use serde_json::Value;
use std::collections::{HashMap, HashSet};
use std::io::{BufRead, BufReader, BufWriter, Write};

fn id(v: &Value, key: &str) -> u64 {
    v[key].as_u64().unwrap()
}

fn render(names: &HashMap<u64, (u64, String)>, i: u64) -> String {
    match names.get(&i) {
        None => String::new(),
        Some((pre, s)) => {
            let p = render(names, *pre);
            if p.is_empty() { s.clone() } else { format!("{p}.{s}") }
        }
    }
}

fn redirect(v: &mut Value, key: &str, alias: &HashMap<u64, u64>) -> bool {
    let Some(target) = v.get(key).and_then(Value::as_u64).and_then(|i| alias.get(&i)) else {
        return false;
    };
    v[key] = Value::from(*target);
    true
}

fn redirect_all(v: &mut Value, keys: &[&str], alias: &HashMap<u64, u64>) -> bool {
    keys.iter().fold(false, |changed, key| redirect(v, key, alias) | changed)
}

fn main() {
    let input = std::env::args().nth(1).unwrap();
    let output = std::env::args().nth(2).unwrap();
    let reader = BufReader::with_capacity(1 << 20, std::fs::File::open(input).unwrap());
    let mut writer = BufWriter::with_capacity(1 << 20, std::fs::File::create(output).unwrap());
    let mut bad_name: HashSet<u64> = HashSet::new();
    let mut declared: HashSet<u64> = HashSet::new();
    let mut bad_expr: Vec<bool> = Vec::new();
    let mut pending: HashMap<u64, Vec<u64>> = HashMap::new();
    let mut name_table: HashMap<u64, (u64, String)> = HashMap::new();
    let mut auto_name: Option<u64> = None;
    let mut auto_const: HashSet<u64> = HashSet::new();
    let mut auto_partial: HashMap<u64, u64> = HashMap::new();
    let mut alias: HashMap<u64, u64> = HashMap::new();
    let (mut total, mut dropped, mut nested, mut erased) = (0u64, 0u64, 0u64, 0u64);
    let kinds = ["axiom", "def", "thm", "opaque", "quot", "inductive"];
    for line in reader.lines() {
        let line = line.unwrap();
        let mut o: Value = serde_json::from_str(&line).unwrap();
        let obj = o.as_object_mut().unwrap();
        if let Some(i) = obj.get("in") {
            let i = i.as_u64().unwrap();
            if let Some(v) = obj.get("str") {
                let s = v["str"].as_str().unwrap().to_owned();
                if id(v, "pre") == 0 && s == "autoParam" {
                    auto_name = Some(i);
                }
                name_table.insert(i, (id(v, "pre"), s));
            } else if let Some(v) = obj.get("num") {
                name_table.insert(i, (id(v, "pre"), id(v, "i").to_string()));
            }
            writeln!(writer, "{line}").unwrap();
            continue;
        }
        if let Some(ie) = obj.get("ie") {
            let i = ie.as_u64().unwrap();
            let (key, v) = obj.iter_mut().find(|(k, _)| k.as_str() != "ie").unwrap();
            let changed = match key.as_str() {
                "proj" => redirect(v, "struct", &alias),
                "app" => redirect_all(v, &["fn", "arg"], &alias),
                "lam" | "forallE" => redirect_all(v, &["type", "body"], &alias),
                "letE" => redirect_all(v, &["type", "value", "body"], &alias),
                "mdata" => redirect(v, "expr", &alias),
                _ => false,
            };
            let mut names: Vec<u64> = Vec::new();
            let mut kids: Vec<u64> = Vec::new();
            match key.as_str() {
                "const" => {
                    names.push(id(v, "name"));
                    if Some(id(v, "name")) == auto_name {
                        auto_const.insert(i);
                    }
                }
                "proj" => {
                    names.push(id(v, "typeName"));
                    kids.push(id(v, "struct"));
                }
                "app" => {
                    let (f, a) = (id(v, "fn"), id(v, "arg"));
                    if auto_const.contains(&f) {
                        auto_partial.insert(i, a);
                    } else if let Some(t) = auto_partial.get(&f) {
                        alias.insert(i, *t);
                        erased += 1;
                    }
                    kids.extend([f, a]);
                }
                "lam" | "forallE" => kids.extend([id(v, "type"), id(v, "body")]),
                "letE" => kids.extend([id(v, "type"), id(v, "value"), id(v, "body")]),
                "mdata" => kids.push(id(v, "expr")),
                _ => {}
            }
            let mut bad = false;
            for c in &kids {
                bad |= bad_expr[*c as usize];
                if let Some(p) = pending.get(c) {
                    names.extend(p.iter().copied());
                }
            }
            bad |= names.iter().any(|x| bad_name.contains(x));
            let mut live: Vec<u64> = names
                .into_iter()
                .filter(|x| !declared.contains(x))
                .collect();
            live.sort_unstable();
            live.dedup();
            let i = i as usize;
            if bad_expr.len() <= i {
                bad_expr.resize(i + 1, false);
            }
            bad_expr[i] = bad;
            if !live.is_empty() {
                pending.insert(i as u64, live);
            }
            if changed {
                writeln!(writer, "{o}").unwrap();
            } else {
                writeln!(writer, "{line}").unwrap();
            }
            continue;
        }
        let Some(kind) = kinds.iter().find(|k| obj.contains_key(**k)) else {
            writeln!(writer, "{line}").unwrap();
            continue;
        };
        let v = obj.get_mut(*kind).unwrap();
        total += 1;
        let root_bad = |r: u64,
                        bad_expr: &Vec<bool>,
                        pending: &HashMap<u64, Vec<u64>>,
                        bad_name: &HashSet<u64>| {
            bad_expr[r as usize]
                || pending
                    .get(&r)
                    .map_or(false, |p| p.iter().any(|x| bad_name.contains(x)))
        };
        let (names, bad, changed) = if *kind == "inductive" {
            let mut changed = false;
            for t in v["types"].as_array_mut().unwrap() {
                changed |= redirect(t, "type", &alias);
            }
            for c in v["ctors"].as_array_mut().unwrap() {
                changed |= redirect(c, "type", &alias);
            }
            for r in v["recs"].as_array_mut().unwrap() {
                changed |= redirect(r, "type", &alias);
                for rule in r["rules"].as_array_mut().unwrap() {
                    changed |= redirect(rule, "rhs", &alias);
                }
            }
            let types = v["types"].as_array().unwrap();
            let ctors = v["ctors"].as_array().unwrap();
            let recs = v["recs"].as_array().unwrap();
            let mut names = Vec::new();
            let mut roots = Vec::new();
            for t in types {
                names.push(id(t, "name"));
                roots.push(id(t, "type"));
            }
            for c in ctors {
                names.push(id(c, "name"));
                roots.push(id(c, "type"));
            }
            for r in recs {
                names.push(id(r, "name"));
                roots.push(id(r, "type"));
                for rule in r["rules"].as_array().unwrap() {
                    roots.push(id(rule, "rhs"));
                }
            }
            let isnested = types
                .iter()
                .any(|t| t["numNested"].as_u64().unwrap_or(0) > 0);
            nested += isnested as u64;
            if isnested {
                for t in types {
                    println!("{}", render(&name_table, id(t, "name")));
                }
            }
            let bad = isnested
                || roots
                    .iter()
                    .any(|r| root_bad(*r, &bad_expr, &pending, &bad_name));
            (names, bad, changed)
        } else {
            let changed = redirect_all(v, &["type", "value"], &alias);
            let bad = ["type", "value"]
                .iter()
                .filter_map(|k| v.get(*k).and_then(|x| x.as_u64()))
                .any(|r| root_bad(r, &bad_expr, &pending, &bad_name));
            (vec![id(v, "name")], bad, changed)
        };
        declared.extend(names.iter().copied());
        if bad {
            dropped += 1;
            bad_name.extend(names);
        } else if changed {
            writeln!(writer, "{o}").unwrap();
        } else {
            writeln!(writer, "{line}").unwrap();
        }
    }
    writer.flush().unwrap();
    eprintln!(
        "total {} nested {} dropped {} autoParam erased {}",
        total, nested, dropped, erased
    );
}
