//! Primitive UI components for the Telltale viewer.

use dioxus::document::eval;
use dioxus::prelude::*;
use dioxus_shadcn::components::badge::{Badge as ShadBadge, BadgeVariant};
use dioxus_shadcn::components::card::Card as ShadCard;
use dioxus_shadcn::components::empty::{Empty, EmptyDescription, EmptyHeader};

#[component]
pub(crate) fn Panel(title: String, subtitle: String, children: Element) -> Element {
    rsx! {
        ShadCard {
            class: Some("tt-panel".to_string()),
            div {
                class: "tt-panel__header",
                h2 { class: "tt-panel__title", "{title}" }
                p { class: "tt-panel__subtitle", "{subtitle}" }
            }
            div { class: "tt-panel__body", {children} }
        }
    }
}

#[component]
pub(crate) fn Card(title: String, subtitle: String, children: Element) -> Element {
    rsx! {
        ShadCard {
            class: Some("tt-card".to_string()),
            h3 { class: "tt-card__title", "{title}" }
            p { class: "tt-card__subtitle", "{subtitle}" }
            div { class: "tt-card__body", {children} }
        }
    }
}

#[component]
pub(crate) fn EmptyState(message: &'static str) -> Element {
    rsx! {
        Empty {
            class: Some("border-0 bg-transparent py-4".to_string()),
            EmptyHeader {
                EmptyDescription { "{message}" }
            }
        }
    }
}

pub(crate) fn badge_variant(tone: &str) -> BadgeVariant {
    match tone {
        "success" => BadgeVariant::Default,
        "warning" => BadgeVariant::Outline,
        _ => BadgeVariant::Secondary,
    }
}

#[component]
pub(crate) fn StatusBadge(tone: &'static str, label: String) -> Element {
    rsx! {
        ShadBadge {
            variant: badge_variant(tone),
            class: Some("font-mono text-[0.6875rem]".to_string()),
            "{label}"
        }
    }
}

#[component]
pub(crate) fn KeyValueLine(label: String, value: String) -> Element {
    rsx! {
        div {
            class: "flex justify-between items-baseline py-0.5 text-xs",
            span { class: "font-sans text-muted-foreground", "{label}" }
            span { class: "font-mono text-foreground", "{value}" }
        }
    }
}

#[component]
pub(crate) fn SidebarSection(title: &'static str, children: Element) -> Element {
    rsx! {
        section {
            class: "mb-4",
            h3 {
                class: "text-[0.625rem] font-sans font-semibold uppercase tracking-[0.08em] text-muted-foreground mb-2 pb-1.5 border-b border-border",
                "{title}"
            }
            {children}
        }
    }
}

#[component]
pub(crate) fn SidebarListItem(label: String, active: bool) -> Element {
    let class = if active {
        "rounded-sm bg-accent px-2.5 py-2 min-w-0 overflow-hidden"
    } else {
        "rounded-sm px-2.5 py-2 min-w-0 overflow-hidden transition-colors hover:bg-accent/60 cursor-pointer"
    };
    rsx! {
        div {
            class: "{class}",
            p { class: "m-0 text-xs text-foreground truncate", "{label}" }
        }
    }
}

#[component]
pub(crate) fn SidebarButton(label: &'static str, onclick: EventHandler<MouseEvent>) -> Element {
    rsx! {
        button {
            r#type: "button",
            class: "inline-flex h-7 w-full items-center justify-center whitespace-nowrap rounded-sm border border-border bg-background px-3 text-xs font-sans font-medium leading-none text-foreground transition-colors hover:bg-accent hover:text-accent-foreground",
            onclick: move |event| onclick.call(event),
            "{label}"
        }
    }
}

/// Format a JSON string with indentation for display.
pub(crate) fn pretty_json(raw: &str) -> String {
    serde_json::from_str::<serde_json::Value>(raw)
        .and_then(|v| serde_json::to_string_pretty(&v))
        .unwrap_or_else(|_| raw.to_string())
}

#[component]
pub(crate) fn CodeBlock(content: String) -> Element {
    let escaped = content
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;");
    rsx! {
        pre {
            class: "font-mono text-[0.6875rem] leading-relaxed text-muted-foreground bg-background rounded-sm px-3 py-2 w-full min-w-0 max-w-full",
            style: "white-space: pre-wrap; word-break: break-word; overflow-wrap: break-word;",
            dangerous_inner_html: escaped,
        }
    }
}

pub(crate) fn nav_tab_class(is_active: bool) -> &'static str {
    if is_active {
        "inline-flex h-8 items-center justify-center whitespace-nowrap rounded-sm bg-accent px-3 text-xs font-sans uppercase leading-none tracking-[0.08em] text-foreground"
    } else {
        "inline-flex h-8 items-center justify-center whitespace-nowrap rounded-sm px-3 text-xs font-sans uppercase leading-none tracking-[0.08em] text-muted-foreground hover:bg-accent hover:text-foreground transition-colors"
    }
}

pub(crate) fn call_js(fn_name: &str, args: &[&str]) {
    let fn_name_json = serde_json::to_string(fn_name).unwrap_or_else(|_| "\"\"".to_string());
    let args_json = serde_json::to_string(args).unwrap_or_else(|_| "[]".to_string());
    let script = format!(
        "const fnRef = globalThis[{fn_name_json}]; if (typeof fnRef === 'function') {{ fnRef(...{args_json}); }}"
    );
    let _ = eval(&script);
}
