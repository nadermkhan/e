#include <iostream>
#include <string>
#include <string_view>
#include <vector>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <functional>
#include <variant>
#include <optional>
#include <fstream>
#include <sstream>
#include <cctype>
#include <cstdint>
#include <cassert>
#include <algorithm>
#include <cstring>
#include <cstdio>

namespace evo {

struct Position {
    size_t offset = 0;
    size_t line = 1;
    size_t column = 1;
};

struct Span {
    Position start;
    Position end;
};

struct Error {
    std::string message;
    Position pos;
};

enum class NodeType {
    Rule, Choice, Sequence, Labeled, Pluck, Action,
    Lookahead, Repetition, StringLiteral, CharClass,
    AnyChar, RuleRef, Text
};

enum class RepKind { ZeroOrMore, OneOrMore, Optional };

class Visitor;

class ASTNode {
public:
    Span span;
    virtual ~ASTNode() = default;
    virtual NodeType type() const = 0;
    virtual void accept(Visitor& v) = 0;
};

class RuleNode;
class ChoiceNode;
class SequenceNode;
class LabeledNode;
class PluckNode;
class ActionNode;
class LookaheadNode;
class RepetitionNode;
class StringLiteralNode;
class CharClassNode;
class AnyCharNode;
class RuleRefNode;
class TextNode;

class Visitor {
public:
    virtual ~Visitor() = default;
    virtual void visit(RuleNode& n) = 0;
    virtual void visit(ChoiceNode& n) = 0;
    virtual void visit(SequenceNode& n) = 0;
    virtual void visit(LabeledNode& n) = 0;
    virtual void visit(PluckNode& n) = 0;
    virtual void visit(ActionNode& n) = 0;
    virtual void visit(LookaheadNode& n) = 0;
    virtual void visit(RepetitionNode& n) = 0;
    virtual void visit(StringLiteralNode& n) = 0;
    virtual void visit(CharClassNode& n) = 0;
    virtual void visit(AnyCharNode& n) = 0;
    virtual void visit(RuleRefNode& n) = 0;
    virtual void visit(TextNode& n) = 0;
};

class RuleNode : public ASTNode {
public:
    std::string name;
    std::string display_name;
    std::unique_ptr<ASTNode> body;
    NodeType type() const override { return NodeType::Rule; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class ChoiceNode : public ASTNode {
public:
    std::vector<std::unique_ptr<ASTNode>> alternatives;
    NodeType type() const override { return NodeType::Choice; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class SequenceNode : public ASTNode {
public:
    std::vector<std::unique_ptr<ASTNode>> elements;
    NodeType type() const override { return NodeType::Sequence; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class LabeledNode : public ASTNode {
public:
    std::string label;
    std::unique_ptr<ASTNode> child;
    NodeType type() const override { return NodeType::Labeled; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class PluckNode : public ASTNode {
public:
    std::unique_ptr<ASTNode> child;
    NodeType type() const override { return NodeType::Pluck; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class ActionNode : public ASTNode {
public:
    std::unique_ptr<ASTNode> expression;
    std::string code;
    NodeType type() const override { return NodeType::Action; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class LookaheadNode : public ASTNode {
public:
    bool is_positive = true;
    std::unique_ptr<ASTNode> child;
    NodeType type() const override { return NodeType::Lookahead; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class RepetitionNode : public ASTNode {
public:
    RepKind kind;
    std::unique_ptr<ASTNode> child;
    NodeType type() const override { return NodeType::Repetition; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class StringLiteralNode : public ASTNode {
public:
    std::string value;
    bool case_insensitive = false;
    NodeType type() const override { return NodeType::StringLiteral; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class CharClassNode : public ASTNode {
public:
    bool inverted = false;
    struct Range { unsigned char lo; unsigned char hi; };
    std::vector<Range> ranges;
    NodeType type() const override { return NodeType::CharClass; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class AnyCharNode : public ASTNode {
public:
    NodeType type() const override { return NodeType::AnyChar; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class RuleRefNode : public ASTNode {
public:
    std::string name;
    NodeType type() const override { return NodeType::RuleRef; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class TextNode : public ASTNode {
public:
    std::unique_ptr<ASTNode> child;
    NodeType type() const override { return NodeType::Text; }
    void accept(Visitor& v) override { v.visit(*this); }
};

class Grammar {
public:
    std::string initializer;
    std::vector<std::unique_ptr<RuleNode>> rules;
};

class MetaParser {
    std::string_view input_;
    size_t cursor_ = 0;
    size_t line_ = 1;
    size_t col_ = 1;
    std::vector<Error> errors_;

    Position pos() const { return {cursor_, line_, col_}; }
    bool atEnd() const { return cursor_ >= input_.size(); }
    char peek() const { return atEnd() ? '\0' : input_[cursor_]; }
    char peekAt(size_t off) const {
        size_t p = cursor_ + off;
        return p < input_.size() ? input_[p] : '\0';
    }

    char advance() {
        if (atEnd()) return '\0'; // Add this safety guard
        char c = input_[cursor_++];
        if (c == '\n') { 
            line_++; 
            col_ = 1; 
        } else if ((static_cast<unsigned char>(c) & 0xC0) != 0x80) { 
            // UTF-8 safe column tracking for the meta-parser
            col_++; 
        }
        return c;
    }

    void skipWS() {
        while (!atEnd()) {
            if (std::isspace(static_cast<unsigned char>(peek()))) {
                advance();
            } else if (peek() == '/' && peekAt(1) == '/') {
                while (!atEnd() && peek() != '\n') advance();
            } else if (peek() == '/' && peekAt(1) == '*') {
                advance(); advance();
                while (!atEnd()) {
                    if (peek() == '*' && peekAt(1) == '/') { advance(); advance(); break; }
                    advance();
                }
            } else {
                break;
            }
        }
    }

    bool match(char c) {
        skipWS();
        if (!atEnd() && peek() == c) { advance(); return true; }
        return false;
    }

    bool matchStr(const char* s) {
        skipWS();
        size_t len = std::strlen(s);
        if (cursor_ + len <= input_.size() && input_.substr(cursor_, len) == s) {
            for (size_t i = 0; i < len; i++) advance();
            return true;
        }
        return false;
    }

    bool lookingAtRuleDef() {
        size_t sc = cursor_, sl = line_, sco = col_;
        skipWS();
        if (atEnd() || (!std::isalpha(static_cast<unsigned char>(peek())) && peek() != '_')) {
            cursor_ = sc; line_ = sl; col_ = sco; return false;
        }
        while (!atEnd() && (std::isalnum(static_cast<unsigned char>(peek())) || peek() == '_')) advance();
        skipWS();
        if (!atEnd() && peek() == '"') {
            advance();
            while (!atEnd() && peek() != '"') advance();
            if (!atEnd()) advance();
            skipWS();
        }
        bool found = (!atEnd() && peek() == '=');
        cursor_ = sc; line_ = sl; col_ = sco;
        return found;
    }

    std::string parseIdentifier() {
        skipWS();
        std::string result;
        if (!atEnd() && (std::isalpha(static_cast<unsigned char>(peek())) || peek() == '_')) {
            result += advance();
            while (!atEnd() && (std::isalnum(static_cast<unsigned char>(peek())) || peek() == '_')) {
                result += advance();
            }
        }
        return result;
    }

    std::string parseDisplayName() {
        skipWS();
        if (atEnd() || peek() != '"') return "";
        advance();
        std::string result;
        while (!atEnd() && peek() != '"') {
            if (peek() == '\\') {
                advance(); // Consume the backslash
                result += parseEscapeChar();
            } else {
                result += advance();
            }
        }
        if (!atEnd()) advance(); // Consume closing quote
        return result;
    }

    std::string parseActionBlock() {
        skipWS();
        if (atEnd() || peek() != '{') return "";
        advance();
        std::string code;
        int depth = 1;
        while (!atEnd() && depth > 0) {
            char c = peek();
            if (c == '{') depth++;
            else if (c == '}') { depth--; if (depth == 0) { advance(); break; } }
            else if (c == 'R' && peekAt(1) == '"') {
                // Basic skip for C++ raw string literals to prevent brace-depth corruption
                code += advance(); // Consume 'R'
                code += advance(); // Consume '"'
                while (!atEnd()) {
                    if (peek() == ')' && peekAt(1) == '"') { // C++ raw string ends with )"
                        code += advance(); code += advance(); break; 
                    }
                    code += advance();
                }
                continue;
            }
            else if (c == '"') {
                code += advance();
                while (!atEnd() && peek() != '"') {
                    if (peek() == '\\') {
                        code += advance();
                        if (!atEnd()) code += advance();
                    } else {
                        code += advance();
                    }
                }
                if (!atEnd()) code += advance();
                continue;
            } else if (c == '\'') {
                code += advance();
                while (!atEnd() && peek() != '\'') {
                    if (peek() == '\\') {
                        code += advance();
                        if (!atEnd()) code += advance();
                    } else {
                        code += advance();
                    }
                }
                if (!atEnd()) code += advance();
                continue;
            } else if (c == '/') {
                if (peekAt(1) == '/') {
                    code += advance(); code += advance();
                    while (!atEnd() && peek() != '\n') code += advance();
                    continue;
                } else if (peekAt(1) == '*') {
                    code += advance(); code += advance();
                    while (!atEnd()) {
                        if (peek() == '*' && peekAt(1) == '/') { 
                            code += advance(); code += advance(); 
                            break; 
                        }
                        code += advance();
                    }
                    continue;
                }
            }
            code += advance();
        }
        return code;
    }

    char parseEscapeChar() {
        if (atEnd()) return '\0';
        char c = advance();
        switch (c) {
            case 'n': return '\n';
            case 'r': return '\r';
            case 't': return '\t';
            case '\\': return '\\';
            case '\'': return '\'';
            case '"': return '"';
            case '[': return '[';
            case ']': return ']';
            case '-': return '-';
            case '0': return '\0';
            case 'x': {
                int val = 0;
                for (int i = 0; i < 2; i++) {
                    if (atEnd()) break;
                    char hc = advance();
                    if (hc >= '0' && hc <= '9') val = val * 16 + (hc - '0');
                    else if (hc >= 'a' && hc <= 'f') val = val * 16 + (hc - 'a' + 10);
                    else if (hc >= 'A' && hc <= 'F') val = val * 16 + (hc - 'A' + 10);
                    else break;
                }
                return static_cast<char>(val);
            }
            default: return c;
        }
    }

    std::unique_ptr<ASTNode> parseChoice() {
        Position start = pos();
        auto first = parseActionExpr();
        if (!first) return nullptr;
        std::vector<std::unique_ptr<ASTNode>> alts;
        alts.push_back(std::move(first));
        while (true) {
            skipWS();
            if (atEnd() || peek() != '/') break;
            advance();
            auto next = parseActionExpr();
            if (!next) {
                errors_.push_back({"Expected expression after '/'", pos()});
                break;
            }
            alts.push_back(std::move(next));
        }
        if (alts.size() == 1) return std::move(alts[0]);
        auto node = std::make_unique<ChoiceNode>();
        node->span.start = start;
        node->span.end = pos();
        node->alternatives = std::move(alts);
        return node;
    }

    std::unique_ptr<ASTNode> parseActionExpr() {
        Position start = pos();
        auto seq = parseSequence();
        if (!seq) return nullptr;
        skipWS();
        if (!atEnd() && peek() == '{') {
            std::string code = parseActionBlock();
            auto node = std::make_unique<ActionNode>();
            node->expression = std::move(seq);
            node->code = code;
            node->span.start = start;
            node->span.end = pos();
            return node;
        }
        return seq;
    }

    std::unique_ptr<ASTNode> parseSequence() {
        Position start = pos();
        std::vector<std::unique_ptr<ASTNode>> elems;
        while (true) {
            skipWS();
            if (atEnd()) break;
            char c = peek();
            if (c == '/' || c == ')' || c == '{' || c == '}') break;
            if (lookingAtRuleDef()) break;
            auto elem = parseLabeledOrPluck();
            if (!elem) break;
            elems.push_back(std::move(elem));
        }
        if (elems.empty()) return nullptr;
        if (elems.size() == 1) return std::move(elems[0]);
        auto node = std::make_unique<SequenceNode>();
        node->span.start = start;
        node->span.end = pos();
        node->elements = std::move(elems);
        return node;
    }

    std::unique_ptr<ASTNode> parseLabeledOrPluck() {
        skipWS();
        Position start = pos();
        if (!atEnd() && peek() == '@') {
            advance();
            auto child = parsePrefix();
            if (!child) { errors_.push_back({"Expected expression after '@'", pos()}); return nullptr; }
            auto node = std::make_unique<PluckNode>();
            node->child = std::move(child);
            node->span.start = start;
            node->span.end = pos();
            return node;
        }
        size_t sc = cursor_, sl = line_, sco = col_;
        std::string ident = parseIdentifier();
        if (!ident.empty()) {
            skipWS();
            if (!atEnd() && peek() == ':') {
                advance();
                auto child = parsePrefix();
                if (!child) { errors_.push_back({"Expected expression after label '" + ident + ":'", pos()}); return nullptr; }
                auto node = std::make_unique<LabeledNode>();
                node->label = ident;
                node->child = std::move(child);
                node->span.start = start;
                node->span.end = pos();
                return node;
            }
            cursor_ = sc; line_ = sl; col_ = sco;
        }
        return parsePrefix();
    }

    std::unique_ptr<ASTNode> parsePrefix() {
        skipWS();
        Position start = pos();
        if (!atEnd() && peek() == '$') {
            advance();
            auto child = parseSuffix();
            if (!child) { errors_.push_back({"Expected expression after '$'", pos()}); return nullptr; }
            auto node = std::make_unique<TextNode>();
            node->child = std::move(child);
            node->span.start = start;
            node->span.end = pos();
            return node;
        }
        if (!atEnd() && peek() == '&') {
            advance();
            auto child = parseSuffix();
            if (!child) { errors_.push_back({"Expected expression after '&'", pos()}); return nullptr; }
            auto node = std::make_unique<LookaheadNode>();
            node->is_positive = true;
            node->child = std::move(child);
            node->span.start = start;
            node->span.end = pos();
            return node;
        }
        if (!atEnd() && peek() == '!') {
            advance();
            auto child = parseSuffix();
            if (!child) { errors_.push_back({"Expected expression after '!'", pos()}); return nullptr; }
            auto node = std::make_unique<LookaheadNode>();
            node->is_positive = false;
            node->child = std::move(child);
            node->span.start = start;
            node->span.end = pos();
            return node;
        }
        return parseSuffix();
    }

    std::unique_ptr<ASTNode> parseSuffix() {
        auto child = parsePrimary();
        if (!child) return nullptr;
        skipWS();
        if (!atEnd()) {
            Position start = child->span.start;
            if (peek() == '*') {
                advance();
                auto node = std::make_unique<RepetitionNode>();
                node->kind = RepKind::ZeroOrMore;
                node->child = std::move(child);
                node->span.start = start;
                node->span.end = pos();
                return node;
            }
            if (peek() == '+') {
                advance();
                auto node = std::make_unique<RepetitionNode>();
                node->kind = RepKind::OneOrMore;
                node->child = std::move(child);
                node->span.start = start;
                node->span.end = pos();
                return node;
            }
            if (peek() == '?') {
                advance();
                auto node = std::make_unique<RepetitionNode>();
                node->kind = RepKind::Optional;
                node->child = std::move(child);
                node->span.start = start;
                node->span.end = pos();
                return node;
            }
        }
        return child;
    }

    std::unique_ptr<ASTNode> parsePrimary() {
        skipWS();
        if (atEnd()) return nullptr;
        Position start = pos();
        char c = peek();
        if (c == '\'') return parseStringSingle();
        if (c == '"') return parseStringDouble();
        if (c == '[') return parseCharClassExpr();
        if (c == '.') {
            advance();
            auto node = std::make_unique<AnyCharNode>();
            node->span.start = start;
            node->span.end = pos();
            return node;
        }
        if (c == '(') {
            advance();
            auto inner = parseChoice();
            skipWS();
            if (!atEnd() && peek() == ')') advance();
            else errors_.push_back({"Expected ')'", pos()});
            return inner;
        }
        if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
            std::string name = parseIdentifier();
            if (name.empty()) return nullptr;
            auto node = std::make_unique<RuleRefNode>();
            node->name = name;
            node->span.start = start;
            node->span.end = pos();
            return node;
        }
        return nullptr;
    }

    std::unique_ptr<ASTNode> parseStringSingle() {
        Position start = pos();
        advance();
        std::string value;
        while (!atEnd() && peek() != '\'') {
            if (peek() == '\\') { advance(); value += parseEscapeChar(); }
            else value += advance();
        }
        if (!atEnd()) advance();
        else errors_.push_back({"Unterminated string literal", pos()});
        bool ci = false;
        skipWS();
        if (!atEnd() && peek() == 'i') { ci = true; advance(); }
        auto node = std::make_unique<StringLiteralNode>();
        node->value = value;
        node->case_insensitive = ci;
        node->span.start = start;
        node->span.end = pos();
        return node;
    }

    std::unique_ptr<ASTNode> parseStringDouble() {
        Position start = pos();
        advance();
        std::string value;
        while (!atEnd() && peek() != '"') {
            if (peek() == '\\') { advance(); value += parseEscapeChar(); }
            else value += advance();
        }
        if (!atEnd()) advance();
        else errors_.push_back({"Unterminated string literal", pos()});
        bool ci = false;
        skipWS();
        if (!atEnd() && peek() == 'i') { ci = true; advance(); }
        auto node = std::make_unique<StringLiteralNode>();
        node->value = value;
        node->case_insensitive = ci;
        node->span.start = start;
        node->span.end = pos();
        return node;
    }

    std::unique_ptr<ASTNode> parseCharClassExpr() {
        Position start = pos();
        advance();
        bool inv = false;
        if (!atEnd() && peek() == '^') { inv = true; advance(); }
        std::vector<CharClassNode::Range> ranges;
        while (!atEnd() && peek() != ']') {
            unsigned char lo;
            if (peek() == '\\') { advance(); lo = static_cast<unsigned char>(parseEscapeChar()); }
            else lo = static_cast<unsigned char>(advance());
            unsigned char hi = lo;
            if (!atEnd() && peek() == '-' && peekAt(1) != ']') {
                advance();
                if (!atEnd()) {
                    if (peek() == '\\') { advance(); hi = static_cast<unsigned char>(parseEscapeChar()); }
                    else hi = static_cast<unsigned char>(advance());
                }
            }
            ranges.push_back({lo, hi});
        }
        if (!atEnd()) advance();
        else errors_.push_back({"Unterminated character class", pos()});
        auto node = std::make_unique<CharClassNode>();
        node->inverted = inv;
        node->ranges = std::move(ranges);
        node->span.start = start;
        node->span.end = pos();
        return node;
    }

public:
    std::optional<Grammar> parse(std::string_view input) {
        input_ = input;
        cursor_ = 0;
        line_ = 1;
        col_ = 1;
        errors_.clear();
        Grammar grammar;
        skipWS();
        if (!atEnd() && peek() == '{') {
            grammar.initializer = parseActionBlock();
        }
        skipWS();
        while (!atEnd()) {
            auto rule = parseRuleDef();
            if (rule) grammar.rules.push_back(std::move(rule));
            else {
                if (errors_.empty()) errors_.push_back({"Unexpected input", pos()});
                break;
            }
            skipWS();
        }
        if (!errors_.empty()) return std::nullopt;
        return grammar;
    }

    std::unique_ptr<RuleNode> parseRuleDef() {
        skipWS();
        Position start = pos();
        std::string name = parseIdentifier();
        if (name.empty()) return nullptr;
        std::string display = parseDisplayName();
        skipWS();
        if (atEnd() || peek() != '=') {
            errors_.push_back({"Expected '=' after rule name '" + name + "'", pos()});
            return nullptr;
        }
        advance();
        auto body = parseChoice();
        if (!body) {
            errors_.push_back({"Expected expression in rule '" + name + "'", pos()});
            return nullptr;
        }
        if (!match(';')) {
            errors_.push_back({"Expected ';' at the end of rule '" + name + "'", pos()});
            return nullptr;
        }
        auto rule = std::make_unique<RuleNode>();
        rule->name = name;
        rule->display_name = display;
        rule->body = std::move(body);
        rule->span.start = start;
        rule->span.end = pos();
        return rule;
    }

    const std::vector<Error>& errors() const { return errors_; }
};



class IsTrivialAnalyzer : public Visitor {
public:
    bool is_trivial = true;
    void visit(RuleNode& n) override { n.body->accept(*this); }
    void visit(ChoiceNode& n) override {
        for (auto& a : n.alternatives) { a->accept(*this); if (!is_trivial) return; }
    }
    void visit(SequenceNode& n) override {
        for (auto& e : n.elements) { e->accept(*this); if (!is_trivial) return; }
    }
    void visit(LabeledNode& n) override { n.child->accept(*this); }
    void visit(PluckNode& n) override { n.child->accept(*this); }
    void visit(ActionNode&) override { is_trivial = false; }
    void visit(LookaheadNode&) override { is_trivial = false; }
    void visit(RepetitionNode&) override { is_trivial = false; }
    void visit(StringLiteralNode&) override {}
    void visit(CharClassNode&) override {}
    void visit(AnyCharNode&) override {}
    void visit(RuleRefNode&) override { is_trivial = false; }
    void visit(TextNode& n) override { n.child->accept(*this); }
};

class CppGenerator : public Visitor {
    std::ostringstream out_;
    int indent_ = 0;
    std::unordered_map<std::string, size_t> rule_ids_;
    size_t temp_counter_ = 0;
    Grammar* grammar_ = nullptr;

    std::string ind() const { return std::string(indent_ * 4, ' '); }
    void line(const std::string& s) { out_ << ind() << s << "\n"; }
    void raw(const std::string& s) { out_ << s; }

    std::string escapeChar(char c) {
        switch (c) {
            case '\\': return "\\\\";
            case '\'': return "\\'";
            case '"': return "\\\"";
            case '\n': return "\\n";
            case '\r': return "\\r";
            case '\t': return "\\t";
            case '\0': return "\\0";
            default:
                if (static_cast<unsigned char>(c) < 32 || static_cast<unsigned char>(c) > 126) {
                    char buf[8];
                    snprintf(buf, sizeof(buf), "\\%03o", static_cast<unsigned char>(c));
                    return buf;
                }
                return std::string(1, c);
        }
    }

    std::string escapeString(const std::string& s) {
        std::string r;
        for (char c : s) r += escapeChar(c);
        return r;
    }

    std::string newTemp() { return "v" + std::to_string(temp_counter_++); }

    std::string current_result_;

public:
    std::string generate(Grammar& grammar) {
        grammar_ = &grammar;
        rule_ids_.clear();
        for (size_t i = 0; i < grammar.rules.size(); i++) {
            rule_ids_[grammar.rules[i]->name] = i;
        }
        out_.str("");
        out_.clear();
        temp_counter_ = 0;

        line("#pragma once");
        line("#include <string>");
        line("#include <string_view>");
        line("#include <vector>");
        line("#include <unordered_map>");
        line("#include <optional>");
        line("#include <functional>");
        line("#include <memory>");
        line("#include <type_traits>");
        line("#include <utility>");
        line("#include <cstdint>");
        line("#include <cstddef>");
        line("#include <cstring>");
        line("#include <stdexcept>");
        line("#include <algorithm>");
        line("#include <sstream>");
        line("#include <iostream>");
        line("#include <cctype>");
        line("");
        if (!grammar.initializer.empty()) {
            line("// User initializer code");
            raw(grammar.initializer);
            raw("\n");
            line("");
        }
        line("namespace EvoParser {");
        line("");
        line("struct Position {");
        line("    size_t offset = 0;");
        line("    size_t line = 1;");
        line("    size_t column = 1;");
        line("};");
        line("");
        line("struct Span {");
        line("    Position start;");
        line("    Position end;");
        line("};");
        line("");
        line("struct ParseError : public std::exception {");
        indent_++;
        line("std::string message;");
        line("Position pos;");
        line("std::string expected;");
        line("std::string full_msg; // No longer mutable");
        line("");
        line("void build_message() {");
        indent_++;
        line("full_msg = message + \" at line \" + std::to_string(pos.line) + \", col \" + std::to_string(pos.column);");
        line("if (!expected.empty()) full_msg += \" (Expected: \" + expected + \")\";");
        indent_--;
        line("}");
        line("");
        line("const char* what() const noexcept override {");
        indent_++;
        line("return full_msg.c_str();");
        indent_--;
        line("}");
        indent_--;
        line("};");
        line("");
        line("enum class ValueType { Null, StringView, Array, Int, Float, Bool };");
        line("");
        line("struct Value {");
        indent_++;
        line("union {");
        indent_++;
        line("struct { const char* ptr; size_t len; } str;");
        line("struct { size_t arena_start; size_t length; } arr;");
        line("int64_t i;");
        line("double f;");
        line("bool b;");
        indent_--;
        line("} data;");
        line("uint32_t line = 0;");
        line("uint32_t col = 0;");
        line("uint32_t length = 0;");
        line("ValueType type = ValueType::Null;");
        line("");
        line("Value() : line(0), col(0), length(0), type(ValueType::Null) { data.str = {nullptr, 0}; }");
        line("Value(std::nullptr_t) : Value() {}");
        line("Value(std::string_view s) : Value() { type = ValueType::StringView; data.str = {s.data(), s.length()}; }");
        line("Value(const char* s) : Value() { type = ValueType::StringView; data.str = {s, std::strlen(s)}; }");
        line("Value(const std::string&) = delete; // Prevent dangling pointers");
        line("Value(int64_t v) : Value() { type = ValueType::Int; data.i = v; }");
        line("Value(int v) : Value() { type = ValueType::Int; data.i = v; }");
        line("Value(unsigned int v) : Value() { type = ValueType::Int; data.i = static_cast<int64_t>(v); }");
        line("Value(unsigned long v) : Value() { type = ValueType::Int; data.i = static_cast<int64_t>(v); }");
        line("Value(unsigned long long v) : Value() { type = ValueType::Int; data.i = static_cast<int64_t>(v); }");
        line("Value(double v) : Value() { type = ValueType::Float; data.f = v; }");
        line("Value(bool v) : Value() { type = ValueType::Bool; data.b = v; }");
        line("Value(const Value&) = default;");
        line("Value& operator=(const Value&) = default;");
        indent_--;
        line("};");
        line("");
        line("// WARNING: Deeply nested left-recursive expressions may temporarily orphan AST nodes in this arena,");
        line("// increasing memory consumption during parsing. The arena is only reset upon full parse failure.");
        line("class ValueArena {");
        line("public:");
        indent_++;
        line("std::vector<std::unique_ptr<std::string>> string_pool;");
        line("std::vector<Value> buffer;");
        line("size_t head = 0;");
        line("ValueArena(size_t capacity = 100000) { buffer.resize(capacity); }");
        line("ValueArena(ValueArena&&) noexcept = default;");
        line("ValueArena& operator=(ValueArena&&) noexcept = default;");
        line("ValueArena(const ValueArena&) = delete;");
        line("ValueArena& operator=(const ValueArena&) = delete;");
        line("size_t allocate(const std::vector<Value>& nodes) {");
        indent_++;
        line("if (head + nodes.size() > buffer.size()) buffer.resize(std::max(buffer.size() * 2, head + nodes.size()));");
        line("size_t start = head;");
        line("for(const auto& n : nodes) buffer[head++] = n;");
        line("return start;");
        indent_--;
        line("}");
        line("void push_back(const Value& val) {");
        indent_++;
        line("if (head >= buffer.size()) buffer.resize(buffer.size() == 0 ? 128 : buffer.size() * 2);");
        line("buffer[head++] = val;");
        indent_--;
        line("}");
        line("size_t save() const { return head; }");
        line("void restore(size_t saved_head) { head = saved_head; }");
        line("const Value* get_array(size_t start) const { return buffer.data() + start; }");
        line("std::string_view allocateString(std::string s) {");
        indent_++;
        line("string_pool.push_back(std::make_unique<std::string>(std::move(s)));");
        line("return *string_pool.back();");
        indent_--;
        line("}");
        indent_--;
        line("};");
        line("");
        line("inline Value makeString(std::string_view s) { return Value(s); }");
        line("inline Value makeDynamicString(ValueArena& arena, std::string s) {");
        indent_++;
        line("return Value(arena.allocateString(std::move(s)));");
        indent_--;
        line("}");
        line("inline Value makeInt(int64_t v) { return Value(v); }");
        line("inline Value makeFloat(double v) { return Value(v); }");
        line("inline Value makeBool(bool v) { return Value(v); }");
        line("inline Value makeNull() { return Value(nullptr); }");
        line("");
        line("inline std::string_view toString(const Value& v) { return std::string_view(v.data.str.ptr, v.data.str.len); }");
        line("inline int64_t toInt(const Value& v) { return v.data.i; }");
        line("inline double toFloat(const Value& v) { return v.data.f; }");
        line("inline bool toBool(const Value& v) { return v.data.b; }");
        line("inline bool isNull(const Value& v) { return v.type == ValueType::Null; }");
        line("");

        line("struct ArrayView {");
        indent_++;
        line("const ValueArena* arena;");
        line("size_t start;");
        line("size_t size;");
        line("");
        line("struct Iterator {");
        indent_++;
        line("const ValueArena* arena;");
        line("size_t idx;");
        line("bool operator!=(const Iterator& o) const { return idx != o.idx; }");
        line("Iterator& operator++() { idx++; return *this; }");
        line("const Value& operator*() const { return arena->buffer[idx]; }");
        indent_--;
        line("};");
        line("");
        line("Iterator begin() const { return {arena, start}; }");
        line("Iterator end() const { return {arena, start + size}; }");
        line("const Value& operator[](size_t i) const { return arena->buffer[start + i]; }");
        indent_--;
        line("};");
        line("");
        line("struct ParseContext {");
        indent_++;
        line("Value root;");
        line("ValueArena arena;");
        line("");
        line("ParseContext() = default;");
        line("ParseContext(Value r, ValueArena&& a) : root(r), arena(std::move(a)) {}");
        line("");
        line("ArrayView getArrayElements(const Value& v) const {");
        indent_++;
        line("if (v.type != ValueType::Array) return {nullptr, 0, 0};");
        line("return {&arena, v.data.arr.arena_start, v.data.arr.length};");
        indent_--;
        line("}");
        indent_--;
        line("};");
        line("");
        line("class Parser {");
        line("public:");
        indent_++;
        line("struct Result {");
        indent_++;
        line("bool success = false;");
        line("Value value;");
        line("size_t end_cursor = 0;");
        line("uint32_t end_line = 1;");
        line("uint32_t end_col = 1;");
        indent_--;
        line("};");
        line("");
        line("ParseContext parse(std::string_view input) {");
        indent_++;
        line("input_ = input;");
        line("cursor_ = 0;");
        line("line_ = 1;");
        line("col_ = 1;");
        line("current_depth_ = 0; // ADD THIS: Reset depth guard on recycle");
        line("if (memo_cache_.empty()) memo_cache_.resize(MEMO_SIZE);");
        line("parse_generation_++;");
        line("if (parse_generation_ == 0) {");
        indent_++;
        line("std::fill(memo_cache_.begin(), memo_cache_.end(), MemoEntry{});");
        line("parse_generation_ = 1;");
        indent_--;
        line("}");
        line("arena_ = ValueArena(100000);");
        line("max_fail_pos_ = 0;");
        line("max_fail_line_ = 1;");
        line("max_fail_col_ = 1;");
        line("expected_.clear();");
        if (!grammar.rules.empty()) {
            line("auto r = parse_" + grammar.rules[0]->name + "();");
            line("if (r.success) {");
            indent_++;
            line("if (cursor_ == input_.size()) return ParseContext(r.value, std::move(arena_));");
            line("else fail(\"End of File (trailing characters found)\");");
            indent_--;
            line("}");
            line("ParseError err;");
            line("err.message = \"Syntax error\";");
            line("err.pos = {max_fail_pos_, max_fail_line_, max_fail_col_};");
            line("if (!expected_.empty()) {");
            indent_++;
            line("for (size_t i = 0; i < expected_.size(); i++) {");
            indent_++;
            line("if (i > 0) err.expected += \", \";");
            line("err.expected += std::string(expected_[i]);");
            indent_--;
            line("}");
            indent_--;
            line("}");
            line("err.build_message();");
            line("throw err;");
        } else {
            line("return ParseContext(makeNull(), std::move(arena_));");
        }
        indent_--;
        line("}");
        line("");
        line("bool try_parse(std::string_view input, ParseContext& out, ParseError& err) {");
        indent_++;
        line("try { out = parse(input); return true; }");
        line("catch (const ParseError& e) { err = e; return false; }");
        line("catch (...) { return false; }");
        indent_--;
        line("}");
        line("");
        line("bool try_parse(std::string_view input, ParseContext& out) {");
        indent_++;
        line("ParseError ignored;");
        line("return try_parse(input, out, ignored);");
        indent_--;
        line("}");
        line("");
        line("// Prevent dangling pointers from temporary strings in the zero-copy architecture");
        line("ParseContext parse(std::string&&) = delete;");
        line("bool try_parse(std::string&&, ParseContext&, ParseError&) = delete;");
        line("bool try_parse(std::string&&, ParseContext&) = delete;");
        line("");
        line("size_t max_fail_pos() const { return max_fail_pos_; }");
        line("size_t max_fail_line() const { return max_fail_line_; }");
        line("size_t max_fail_col() const { return max_fail_col_; }");

        line("Value createArray(const std::vector<Value>& elements) {");
        indent_++;
        line("Value val;");
        line("val.type = ValueType::Array;");
        line("val.data.arr.arena_start = arena_.allocate(elements);");
        line("val.data.arr.length = static_cast<uint32_t>(elements.size());");
        line("return val;");
        indent_--;
        line("}");
        line("");

        line("ArrayView getArrayElements(const Value& v) const {");
        indent_++;
        line("if (v.type != ValueType::Array) return {nullptr, 0, 0};");
        line("return {&arena_, v.data.arr.arena_start, v.data.arr.length};");
        indent_--;
        line("}");
        line("");


        indent_--;
        line("");
        line("private:");
        indent_++;
        line("std::string_view input_;");
        line("size_t cursor_ = 0;");
        line("size_t line_ = 1;");
        line("size_t col_ = 1;");
        line("size_t max_fail_pos_ = 0;");
        line("size_t max_fail_line_ = 1;");
        line("size_t max_fail_col_ = 1;");
        line("std::vector<std::string_view> expected_;");
        line("");
        line("static constexpr size_t MEMO_SIZE = 1024 * 1024;");
        line("static constexpr size_t MEMO_MASK = MEMO_SIZE - 1;");
        line("struct MemoEntry {");
        indent_++;
        line("uint64_t key = 0;");
        line("size_t generation = 0;");
        line("bool active = false; // O(1) Cycle Detection Tracker");
        line("Result result;");
        indent_--;
        line("};");
        line("std::vector<MemoEntry> memo_cache_;");
        line("ValueArena arena_;");
        line("size_t parse_generation_ = 0;");
        line("size_t current_depth_ = 0;");
        line("static constexpr size_t MAX_DEPTH = 2000;");
        line("");
        line("bool at_end() const { return cursor_ >= input_.size(); }");
        line("char peek() const { return at_end() ? '\\0' : input_[cursor_]; }");
        line("");
        line("char advance_char() {");
        indent_++;
        line("char c = input_[cursor_++];");
        line("if (c == '\\n') { line_++; col_ = 1; }");
        line("else if ((static_cast<unsigned char>(c) & 0xC0) != 0x80) { col_++; } // UTF-8 safe column tracking");
        line("return c;");
        indent_--;
        line("}");
        line("");
        line("void save(size_t& c, size_t& l, size_t& co, size_t& ar) const { c = cursor_; l = line_; co = col_; ar = arena_.save(); }");
        line("void restore(size_t c, size_t l, size_t co, size_t ar) { cursor_ = c; line_ = l; col_ = co; (void)ar; /* Arena is monotonic to preserve memoized ASTs */ }");
        line("");
        line("void fail(std::string_view exp) {");
        indent_++;
        line("if (cursor_ > max_fail_pos_) {");
        indent_++;
        line("max_fail_pos_ = cursor_;");
        line("max_fail_line_ = line_;");
        line("max_fail_col_ = col_;");
        line("expected_.clear();");
        line("expected_.push_back(exp);");
        indent_--;
        line("} else if (cursor_ == max_fail_pos_) {");
        indent_++;
        line("if (std::find(expected_.begin(), expected_.end(), exp) == expected_.end()) {");
        indent_++;
        line("expected_.push_back(exp);");
        indent_--;
        line("}");
        indent_--;
        line("}");
        indent_--;
        line("}");
        line("");
        line("std::string_view text_at(size_t start, size_t end) const {");
        indent_++;
        line("return input_.substr(start, end - start);");
        indent_--;
        line("}");
        line("");



        for (auto& rule : grammar.rules) {
            emitRule(*rule);
        }

        indent_--;
        line("};");
        line("");
        line("} // namespace EvoParser");

        return out_.str();
    }

private:
    void emitRule(RuleNode& rule) {
        IsTrivialAnalyzer trivial_analyzer;
        rule.body->accept(trivial_analyzer);
        bool trivial = trivial_analyzer.is_trivial;

        size_t rid = rule_ids_[rule.name];
        line("Result parse_" + rule.name + "() {");
        indent_++;

        line("uint64_t memo_key = (static_cast<uint64_t>(" + std::to_string(rid) + "ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);");
        line("size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ " + std::to_string(rid) + "ULL) & MEMO_MASK;");
        if (!trivial) {
            line("if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {");
            indent_++;
            line("if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};");
            line("auto& cached = memo_cache_[memo_idx].result;");

            line("if (cached.success) {");
            indent_++;
            line("cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;");
            line("return cached;");
            indent_--;
            line("}");
            line("return cached;");
            indent_--;
            line("}");
        }

        line("size_t sc = 0, sl = 0, sco = 0, sar = 0;");
        line("save(sc, sl, sco, sar);");
        
        if (trivial) {
            // Fast-path for non-recursive token rules
            std::string res = emitExpr(*rule.body);
            line("if (" + res + "_ok) {");
            indent_++;
            line("return {true, " + res + "_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};");
            indent_--;
            line("} else {");
            indent_++;
            if (!rule.display_name.empty()) line("fail(\"" + escapeString(rule.display_name) + "\");");
            else line("fail(\"" + escapeString(rule.name) + "\");");
            line("restore(sc, sl, sco, sar);");
            line("return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};");
            indent_--;
            line("}");
        } else {
            // Complex path for left-recursive and memoized rules
            line("if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {");
            indent_++;
            line("return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};");
            indent_--;
            line("}");
            
            line("if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail(\"Maximum parse depth exceeded\"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }");
            
            line("memo_cache_[memo_idx].key = memo_key;");
            line("memo_cache_[memo_idx].generation = parse_generation_;");
            line("memo_cache_[memo_idx].active = true;");

            line("auto eval_body = [&]() -> Result {");
            indent_++;
            std::string res = emitExpr(*rule.body);
            line("if (" + res + "_ok) return {true, " + res + "_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};");
            line("return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};");
            indent_--;
            line("};");

            line("Result rule_res = eval_body();");

            line("if (rule_res.success) {");
            indent_++;
            line("memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};");
            line("for (;;) {");
            indent_++;
            line("cursor_ = sc; line_ = sl; col_ = sco;");
            line("Result next_res = eval_body();");
            line("if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {");
            indent_++;
            line("cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;");
            line("break;");
            indent_--;
            line("}");
            line("rule_res = next_res;");
            line("memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};");
            indent_--;
            line("}");
            indent_--;
            line("} else {");
            indent_++;
            if (!rule.display_name.empty()) line("fail(\"" + escapeString(rule.display_name) + "\");");
            else line("fail(\"" + escapeString(rule.name) + "\");");
            line("restore(sc, sl, sco, sar);");
            indent_--;
            line("}");

            line("memo_cache_[memo_idx].active = false;");
            line("current_depth_--;");
            
            line("if (rule_res.success) {");
            line("    memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};");
            line("}");

            line("return rule_res;");
        }
        indent_--;
        line("}");
        line("");
    }

    std::string emitExpr(ASTNode& node) {
        current_result_.clear();
        node.accept(*this);
        return current_result_;
    }

    void visit(RuleNode&) override {}

    void visit(ChoiceNode& n) override {
        std::string name = newTemp();
        line("bool " + name + "_ok = false;");
        line("Value " + name + "_val = makeNull();");
        line("{");
        indent_++;
        line("size_t cc = 0, cl = 0, cco = 0, car = 0;");
        line("save(cc, cl, cco, car);");
        
        for (size_t i = 0; i < n.alternatives.size(); i++) {
            line("if (!" + name + "_ok) {");
            indent_++;
            if (i > 0) line("restore(cc, cl, cco, car);");
            
            line("{");
            indent_++;
            std::string alt = emitExpr(*n.alternatives[i]);
            line("if (" + alt + "_ok) { " + name + "_ok = true; " + name + "_val = " + alt + "_val; }");
            indent_--;
            line("}");
            
            indent_--;
            line("}");
        }
        
        indent_--;
        line("}");
        current_result_ = name;
    }

    void visit(SequenceNode& n) override {
        std::string name = newTemp();
        bool has_labels = false;
        bool has_plucks = false;
        std::vector<std::string> labels;
        
        for (size_t i = 0; i < n.elements.size(); i++) {
            if (n.elements[i]->type() == NodeType::Labeled) {
                has_labels = true;
                labels.push_back(static_cast<LabeledNode&>(*n.elements[i]).label);
            }
            if (n.elements[i]->type() == NodeType::Pluck) {
                has_plucks = true;
            }
        }
        
        line("bool " + name + "_ok = true;");
        line("Value " + name + "_val = makeNull();");
        
        std::string ss = name + "_ss", sls = name + "_sls", scs = name + "_scs", sars = name + "_sars";
        line("size_t " + ss + " = 0, " + sls + " = 0, " + scs + " = 0, " + sars + " = 0;");
        line("save(" + ss + ", " + sls + ", " + scs + ", " + sars + ");");
        
        // C++ array to hold values across block scopes
        line("Value " + name + "_elems[" + std::to_string(std::max<size_t>(1, n.elements.size())) + "];");
        
        if (has_labels) {
            for (auto& lbl : labels) {
                line("Value lbl_" + lbl + " = makeNull();");
            }
        }
        
        std::vector<size_t> pluck_indices;
        for (size_t i = 0; i < n.elements.size(); i++) {
            if (n.elements[i]->type() == NodeType::Pluck) pluck_indices.push_back(i);
            line("if (" + name + "_ok) {");
            indent_++;
            std::string ev = emitExpr(*n.elements[i]);
            line("if (!" + ev + "_ok) { " + name + "_ok = false; restore(" + ss + ", " + sls + ", " + scs + ", " + sars + "); }");
            line("else { " + name + "_elems[" + std::to_string(i) + "] = " + ev + "_val; }");
            
            if (n.elements[i]->type() == NodeType::Labeled) {
                std::string lbl = static_cast<LabeledNode&>(*n.elements[i]).label;
                line("if (" + name + "_ok) lbl_" + lbl + " = " + name + "_elems[" + std::to_string(i) + "];");
            }
            indent_--;
            line("}");
        }
        
        // Packaging the results
        line("if (" + name + "_ok) {");
        indent_++;
        if (has_plucks) {
            if (pluck_indices.size() == 1) {
                line(name + "_val = " + name + "_elems[" + std::to_string(pluck_indices[0]) + "];");
            } else {
                line("size_t seq_start = arena_.head;");
                for (size_t idx : pluck_indices) {
                    line("arena_.push_back(" + name + "_elems[" + std::to_string(idx) + "]);");
                }
                line(name + "_val.type = ValueType::Array;");
                line(name + "_val.data.arr.arena_start = seq_start;");
                line(name + "_val.data.arr.length = static_cast<uint32_t>(" + std::to_string(pluck_indices.size()) + ");");
            }
        } else if (n.elements.size() > 1) {
            line("size_t seq_start = arena_.head;");
            for (size_t i = 0; i < n.elements.size(); i++) {
                line("arena_.push_back(" + name + "_elems[" + std::to_string(i) + "]);");
            }
            line(name + "_val.type = ValueType::Array;");
            line(name + "_val.data.arr.arena_start = seq_start;");
            line(name + "_val.data.arr.length = static_cast<uint32_t>(" + std::to_string(n.elements.size()) + ");");
        } else if (n.elements.size() == 1) {
            line(name + "_val = " + name + "_elems[0];");
        }
        indent_--;
        line("}");
        
        if (has_labels) {
            for (auto& lbl : labels) line("(void)lbl_" + lbl + ";");
        }
        current_result_ = name;
    }

    void visit(LabeledNode& n) override {
        std::string child_res = emitExpr(*n.child);
        current_result_ = child_res;
    }

    void visit(PluckNode& n) override {
        std::string child_res = emitExpr(*n.child);
        current_result_ = child_res;
    }

    void visit(ActionNode& n) override {
        std::string name = newTemp();
        line("size_t " + name + "_start = cursor_;");
        line("size_t " + name + "_startLine = line_;");
        line("size_t " + name + "_startCol = col_;");
        std::string expr_res = emitExpr(*n.expression);

        std::vector<std::string> labels;
        gatherLabels(*n.expression, labels);

        line("bool " + name + "_ok = " + expr_res + "_ok;");
        line("(void)" + expr_res + "_val;");
        line("Value " + name + "_val = makeNull();");
        line("if (" + name + "_ok) {");
        indent_++;

        std::string processed = processActionCode(n.code, labels, expr_res);
        line("auto _text = [&]() -> std::string_view {");
        indent_++;
        line("(void)0;");
        line("return text_at(" + name + "_start, cursor_);");
        indent_--;
        line("};");
        line("(void)_text;");

        for (auto& lbl : labels) {
            line("auto& " + lbl + " = lbl_" + lbl + ";");
            line("(void)" + lbl + ";");
        }

        line(name + "_val = [&]() -> Value {");
        indent_++;
        out_ << ind() << processed << "\n";
        indent_--;
        line("}();");
        line("if (" + name + "_val.line == 0) {");
        indent_++;
        line(name + "_val.line = static_cast<uint32_t>(" + name + "_startLine);");
        line(name + "_val.col = static_cast<uint32_t>(" + name + "_startCol);");
        line(name + "_val.length = static_cast<uint32_t>(cursor_ - " + name + "_start);");
        indent_--;
        line("}");
        indent_--;
        line("}");
        current_result_ = name;
    }

    void gatherLabels(ASTNode& node, std::vector<std::string>& labels) {
        if (node.type() == NodeType::Labeled) {
            labels.push_back(static_cast<LabeledNode&>(node).label);
        } else if (node.type() == NodeType::Sequence) {
            for (auto& e : static_cast<SequenceNode&>(node).elements) {
                gatherLabels(*e, labels);
            }
        } else if (node.type() == NodeType::Action) {
            gatherLabels(*static_cast<ActionNode&>(node).expression, labels);
        } else if (node.type() == NodeType::Choice) {
            for (auto& a : static_cast<ChoiceNode&>(node).alternatives) {
                gatherLabels(*a, labels);
            }
        } else if (node.type() == NodeType::Repetition) {
            gatherLabels(*static_cast<RepetitionNode&>(node).child, labels);
        }
    }

    std::string processActionCode(const std::string& code, const std::vector<std::string>&,
                                  const std::string&) {
        size_t start = 0;
        while (start < code.size() && std::isspace(static_cast<unsigned char>(code[start]))) {
            start++;
        }
        if (start == code.size()) return ""; // String is entirely whitespace
        
        size_t end = code.size();
        while (end > start && std::isspace(static_cast<unsigned char>(code[end - 1]))) {
            end--;
        }
        return code.substr(start, end - start);
    }

    void visit(LookaheadNode& n) override {
        std::string name = newTemp();
        line("bool " + name + "_ok = false;");
        line("Value " + name + "_val = makeNull();");
        line("{");
        indent_++;
        line("size_t lc = 0, ll = 0, lco = 0, lar = 0;");
        line("save(lc, ll, lco, lar);");
        std::string child_res = emitExpr(*n.child);
        line("restore(lc, ll, lco, lar);");
        if (n.is_positive) {
            line(name + "_ok = " + child_res + "_ok;");
        } else {
            line(name + "_ok = !" + child_res + "_ok;");
        }
        indent_--;
        line("}");
        current_result_ = name;
    }

    void visit(RepetitionNode& n) override {
        std::string name = newTemp();
        if (n.kind == RepKind::ZeroOrMore) {
            line("bool " + name + "_ok = true;");
            line("Value " + name + "_val = makeNull();");
            line("{");
            indent_++;
            line("size_t rep_start = arena_.head;");
            line("size_t rep_count = 0;");
            line("for (;;) {");
            indent_++;
            line("size_t rc = 0, rl = 0, rco = 0, rar = 0;");
            line("save(rc, rl, rco, rar);");
            std::string child_res = emitExpr(*n.child);
            line("if (!" + child_res + "_ok) { restore(rc, rl, rco, rar); break; }");
            line("if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak");
            line("arena_.push_back(" + child_res + "_val);");
            line("rep_count++;");
            indent_--;
            line("}");
            line(name + "_val.type = ValueType::Array;");
            line(name + "_val.data.arr.arena_start = rep_start;");
            line(name + "_val.data.arr.length = static_cast<uint32_t>(rep_count);");
            indent_--;
            line("}");
        } else if (n.kind == RepKind::OneOrMore) {
            line("bool " + name + "_ok = false;");
            line("Value " + name + "_val = makeNull();");
            line("{");
            indent_++;
            line("size_t rep_start = arena_.head;");
            line("size_t rep_count = 0;");
            std::string first = emitExpr(*n.child);
            line("if (" + first + "_ok) {");
            indent_++;
            line("arena_.push_back(" + first + "_val);");
            line("rep_count++;");
            line("for (;;) {");
            indent_++;
            line("size_t rc = 0, rl = 0, rco = 0, rar = 0;");
            line("save(rc, rl, rco, rar);");
            std::string next = emitExpr(*n.child);
            line("if (!" + next + "_ok) { restore(rc, rl, rco, rar); break; }");
            line("if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak");
            line("arena_.push_back(" + next + "_val);");
            line("rep_count++;");
            indent_--;
            line("}");
            line(name + "_ok = true;");
            line(name + "_val.type = ValueType::Array;");
            line(name + "_val.data.arr.arena_start = rep_start;");
            line(name + "_val.data.arr.length = static_cast<uint32_t>(rep_count);");
            indent_--;
            line("}"); // Close the successful 'if' block. No empty else needed.
            indent_--;
            line("}");
        } else {
            line("bool " + name + "_ok = true;");
            line("Value " + name + "_val = makeNull();");
            line("{");
            indent_++;
            line("size_t rc = 0, rl = 0, rco = 0, rar = 0;");
            line("save(rc, rl, rco, rar);");
            std::string child_res = emitExpr(*n.child);
            line("if (" + child_res + "_ok) { " + name + "_val = " + child_res + "_val; }");
            line("else { restore(rc, rl, rco, rar); }");
            indent_--;
            line("}");
        }
        current_result_ = name;
    }

    void visit(StringLiteralNode& n) override {
        std::string name = newTemp();
        std::string escaped = escapeString(n.value);
        std::string len = std::to_string(n.value.size());
        line("bool " + name + "_ok = false;");
        line("Value " + name + "_val = makeNull();");
        if (n.value.empty()) {
            line(name + "_ok = true;");
            line(name + "_val = makeString(\"\");");
        } else if (n.case_insensitive) {
            line("{");
            indent_++;
            line("bool match = cursor_ + " + len + " <= input_.size();");
            line("if (match) {");
            indent_++;
            line("for (size_t i = 0; i < " + len + "; i++) {");
            indent_++;
            line("if (std::tolower(static_cast<unsigned char>(input_[cursor_ + i])) != std::tolower(static_cast<unsigned char>(\"" + escaped + "\"[i]))) { match = false; break; }");
            indent_--;
            line("}");
            indent_--;
            line("}");
            line("if (match) {");
            indent_++;
            line("size_t s = cursor_; (void)s;");
            line("for (size_t i = 0; i < " + len + "; i++) advance_char();");
            line(name + "_ok = true;");
            line(name + "_val = makeString(text_at(s, cursor_));");
            indent_--;
            line("} else {");
            indent_++;
            line("fail(\"\\\"" + escaped + "\\\"\");");
            indent_--;
            line("}");
            indent_--;
            line("}");
        } else {
            line("if (cursor_ + " + len + " <= input_.size() && input_.substr(cursor_, " + len + ") == std::string_view(\"" + escaped + "\", " + len + ")) {");
            indent_++;
            line("size_t s = cursor_; (void)s;");
            line("for (size_t i = 0; i < " + len + "; i++) advance_char();");
            line(name + "_ok = true;");
            line(name + "_val = makeString(\"" + escaped + "\");");
            indent_--;
            line("} else {");
            indent_++;
            line("fail(\"\\\"" + escaped + "\\\"\");");
            indent_--;
            line("}");
        }
        current_result_ = name;
    }

    void visit(CharClassNode& n) override {
        std::string name = newTemp();
        line("bool " + name + "_ok = false;");
        line("Value " + name + "_val = makeNull();");
        std::string desc;
        if (n.inverted) desc = "[^";
        else desc = "[";
        for (auto& r : n.ranges) {
            desc += escapeChar(r.lo);
            if (r.lo != r.hi) { desc += "-"; desc += escapeChar(r.hi); }
        }
        desc += "]";

        line("if (!at_end()) {");
        indent_++;
        std::string ch = name + "_ch";
        line("unsigned char " + ch + " = static_cast<unsigned char>(peek());");
        line("bool match = false;");
        line("switch (" + ch + ") {");
        indent_++;
        
        // Deduplicate overlapping ranges to prevent C++ compiler errors
        bool chars[256] = {false};
        bool has_any = false;
        for (const auto& r : n.ranges) {
            for (int c = r.lo; c <= r.hi; c++) {
                chars[c] = true;
                has_any = true;
            }
        }
        
        if (has_any) {
            for (int c = 0; c < 256; c++) {
                if (chars[c]) {
                    line("case " + std::to_string(c) + ":");
                }
            }
            line("    match = true; break;");
        }
        
        indent_--;
        line("}");
        
        std::string full_cond = n.inverted ? "!match" : "match";
        line("if (" + full_cond + ") {");
        indent_++;
        line("size_t start_c = cursor_; (void)start_c;");
        line("advance_char();");
        line(name + "_ok = true;");
        line(name + "_val = makeString(text_at(start_c, cursor_));");
        indent_--;
        line("} else {");
        indent_++;
        line("fail(\"" + escapeString(desc) + "\");");
        indent_--;
        line("}");
        indent_--;
        line("} else {");
        indent_++;
        line("fail(\"" + escapeString(desc) + "\");");
        indent_--;
        line("}");
        current_result_ = name;
    }

    void visit(AnyCharNode&) override {
        std::string name = newTemp();
        line("bool " + name + "_ok = !at_end();");
        line("Value " + name + "_val = makeNull();");
        line("if (" + name + "_ok) {");
        indent_++;
        line("size_t start_c = cursor_; (void)start_c;");
        line("unsigned char c = static_cast<unsigned char>(peek());");
        line("int bytes = 1;");
        line("if ((c & 0xE0) == 0xC0) bytes = 2;");
        line("else if ((c & 0xF0) == 0xE0) bytes = 3;");
        line("else if ((c & 0xF8) == 0xF0) bytes = 4;");
        
        line("for (int i = 0; i < bytes; i++) {");
        indent_++;
        line("if (at_end()) { " + name + "_ok = false; break; }");
        line("advance_char();");
        indent_--;
        line("}");
        
        line("if (" + name + "_ok) {");
        indent_++;
        line(name + "_val = makeString(text_at(start_c, cursor_));");
        indent_--;
        line("} else {");
        indent_++;
        line("cursor_ = start_c; // Rollback on malformed UTF-8 EOF");
        line("fail(\"any character\");");
        indent_--;
        line("}");
        
        indent_--;
        line("} else {");
        indent_++;
        line("fail(\"any character\");");
        indent_--;
        line("}");
        current_result_ = name;
    }

    void visit(RuleRefNode& n) override {
        std::string name = newTemp();
        line("auto " + name + "_r = parse_" + n.name + "();");
        line("bool " + name + "_ok = " + name + "_r.success;");
        line("Value " + name + "_val = " + name + "_r.value;");
        current_result_ = name;
    }

    void visit(TextNode& n) override {
        std::string name = newTemp();
        line("bool " + name + "_ok = false;");
        line("Value " + name + "_val = makeNull();");
        line("{");
        indent_++;
        line("size_t ts = cursor_;");
        // Removed arena save/restore to protect memoized cache pointers
        std::string child_res = emitExpr(*n.child);
        line("if (" + child_res + "_ok) {");
        indent_++;
        line("(void)" + child_res + "_val;");
        line(name + "_ok = true;");
        line(name + "_val = makeString(text_at(ts, cursor_));");
        indent_--;
        line("}");
        indent_--;
        line("}");
        current_result_ = name;
    }
};

} // namespace evo

int main(int argc, char** argv) {
    if (argc < 4) {
        std::cerr << "Usage: evo <input.evo> -o <output.hpp>\n";
        return 1;
    }
    std::string input_file;
    std::string output_file;
    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        if (arg == "-o" && i + 1 < argc) {
            output_file = argv[++i];
        } else if (input_file.empty()) {
            input_file = arg;
        } else {
            std::cerr << "Unknown argument: " << arg << "\n";
            return 1;
        }
    }
    if (input_file.empty() || output_file.empty()) {
        std::cerr << "Usage: evo <input.evo> -o <output.hpp>\n";
        return 1;
    }
    std::ifstream ifs(input_file);
    if (!ifs) {
        std::cerr << "Error: Cannot open '" << input_file << "'\n";
        return 1;
    }
    std::ostringstream ss;
    ss << ifs.rdbuf();
    std::string source = ss.str();
    ifs.close();
    evo::MetaParser parser;
    auto grammar_opt = parser.parse(source);
    if (!grammar_opt) {
        for (auto& err : parser.errors()) {
            std::cerr << input_file << ":" << err.pos.line << ":" << err.pos.column << ": error: " << err.message << "\n";
        }
        return 1;
    }
    evo::CppGenerator gen;
    std::string output = gen.generate(*grammar_opt);
    std::ofstream ofs(output_file);
    if (!ofs) {
        std::cerr << "Error: Cannot open '" << output_file << "'\n";
        return 1;
    }
    ofs << output;
    ofs.close();
    std::cout << "Generated " << output_file << " (" << grammar_opt->rules.size() << " rules)\n";
    return 0;
}