# Ephapax HTTP Server Design

## Purpose

Demonstrate real-world Ephapax usage with linear types for:
- Connection lifecycle management
- Request/response handling
- Resource cleanup guarantees
- Memory safety without GC

## Core Abstraction

```ephapax
// Connection must be handled exactly once (linear)
type Connection@r = Linear {
    socket: Socket@r,
    buffer: Buffer@r
}

// Request owns its body (must be consumed)
type Request@r = Linear {
    method: Method,
    path: String@r,
    headers: Headers@r,
    body: Body@r
}

// Response must be sent exactly once
type Response@r = Linear {
    status: Status,
    headers: Headers@r,
    body: Body@r
}
```

## Handler Types

```ephapax
// Handler must consume request and produce response
type Handler@r = fn(Request@r) -> Response@r

// Middleware transforms handlers (linear function composition)
type Middleware@r = fn(Handler@r) -> Handler@r
```

## Linear Guarantees

### 1. Connection Cleanup
```ephapax
fn handle_connection(conn: Connection@r) -> Unit {
    let! req = read_request(&conn);  // Borrow connection
    let! resp = handle(req);          // Consume request
    write_response(&conn, resp);      // Consume response
    drop(conn);                       // Explicit cleanup
    unit
}
```

**Guaranteed**: Connection always closed (no leaks)

### 2. Request Lifecycle
```ephapax
fn handle_post(req: Request@r) -> Response@r {
    match req.method {
        Post => {
            let! body = req.body;     // Extract body
            let data = parse(body);    // Consume body
            process(data);             // Use data
            ok_response()              // Return response
        },
        _ => method_not_allowed()
    }
}
```

**Guaranteed**: Request body consumed exactly once

### 3. Response Sending
```ephapax
fn send_json(data: Data@r) -> Response@r {
    let! json = serialize(data);  // Consume data
    let! body = Body::from_string(json);
    Response {
        status: Ok,
        headers: json_headers(),
        body: body  // Body ownership transferred
    }
}
```

**Guaranteed**: Response sent exactly once, no double-send

## Affine Mode for Prototyping

```ephapax
// Affine: can drop connections (for testing)
fn prototype_handler(conn: Connection@r) -> Unit {
    let req = try_read(&conn);  // May fail
    // If read fails, conn dropped automatically - OK for prototyping
    unit
}
```

**Use case**: Rapid prototyping, test harnesses

**Migration path**: Add `!` to make linear once stable

## MVP Implementation

### Phase 1: Core Types
- [ ] Socket wrapper
- [ ] Buffer management
- [ ] Request/Response types
- [ ] Connection lifecycle

### Phase 2: Handlers
- [ ] Handler trait
- [ ] Routing (path matching)
- [ ] Method dispatch
- [ ] Error handling

### Phase 3: Middleware
- [ ] Logging
- [ ] CORS
- [ ] Authentication
- [ ] Rate limiting

### Phase 4: WASI Integration
- [ ] TCP socket support
- [ ] File I/O
- [ ] Environment variables
- [ ] Signal handling

## Example Server

```ephapax
fn main() -> i32 {
    region r:
        let! server = Server::bind@r("127.0.0.1:8080");

        server.route("/", get_handler);
        server.route("/api/hello", hello_handler);
        server.route("/api/echo", echo_handler);

        let! result = server.run();
        drop(result);
        0
}

fn hello_handler(req: Request@r) -> Response@r {
    let! body = Body::from_str@r("Hello, Ephapax!");
    Response {
        status: Ok,
        headers: text_headers@r(),
        body: body
    }
}

fn echo_handler(req: Request@r) -> Response@r {
    let! req_body = req.body;
    let! resp_body = Body::copy@r(req_body);
    drop(req_body);
    Response {
        status: Ok,
        headers: text_headers@r(),
        body: resp_body
    }
}
```

## Safety Properties

**Linear Mode**:
- ✅ No connection leaks
- ✅ No double-send responses
- ✅ Request bodies always consumed
- ✅ Memory freed exactly once
- ✅ Compile-time guarantees

**Affine Mode**:
- ✅ No double-send responses
- ✅ Memory freed at most once
- ⚠️  May leak connections (if dropped early)
- ⚠️  May not consume request bodies

## Performance Target

- Throughput: 50K req/sec (single core)
- Latency: <1ms p50, <10ms p99
- Memory: O(connections) with no leaks
- CPU: Comparable to Rust servers
- Size: <100KB WASM binary

## Testing Strategy

1. **Unit tests**: Handler functions
2. **Integration tests**: Full request/response cycle
3. **Property tests**: Connection cleanup, no leaks
4. **Benchmark**: vs Rust Actix/Axum
5. **Conformance**: HTTP/1.1 spec

## Comparison

| Feature | Ephapax Linear | Rust | Node.js |
|---------|----------------|------|---------|
| Memory safety | Compile-time | Compile-time | Runtime |
| Leak prevention | Guaranteed | Guaranteed | No |
| Resource cleanup | Explicit | RAII | GC |
| Performance | Native | Native | JIT |
| Deployment | WASM | Binary | JS runtime |

## Next Steps

1. Implement Socket bindings (WASI)
2. Write Request/Response parsers
3. Build routing system
4. Add middleware support
5. Benchmark and optimize
