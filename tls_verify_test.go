package req

import (
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/hex"
	"encoding/pem"
	"errors"
	"io"
	"log"
	"math/big"
	"net"
	"net/http"
	"net/http/httptest"
	"sync/atomic"
	"testing"
	"time"
)

// emSign Root TLS CA - G3 and EM OV TLS CA - G3C, one of the intermediates it
// signed whose private key was compromised (CVE-2026-111943), copied from
// OkHttp's CompromisedIntermediateTest. The intermediate's private key is the
// scalar 4, so a test can issue a leaf that chains to the real root.
const (
	emsignRootTLSCAG3 = `-----BEGIN CERTIFICATE-----
MIICKTCCAa+gAwIBAgIQDnYGcvFDRZ/I/gqwvAXjlDAKBggqhkjOPQQDAzBWMQsw
CQYDVQQGEwJJTjElMCMGA1UECgwcZU11ZGhyYSBUZWNobm9sb2dpZXMgTGltaXRl
ZDEgMB4GA1UEAwwXZW1TaWduIFJvb3QgVExTIENBIC0gRzMwHhcNMjQwMjA4MDgx
OTMyWhcNNDkwMjA3MDgxOTMyWjBWMQswCQYDVQQGEwJJTjElMCMGA1UECgwcZU11
ZGhyYSBUZWNobm9sb2dpZXMgTGltaXRlZDEgMB4GA1UEAwwXZW1TaWduIFJvb3Qg
VExTIENBIC0gRzMwdjAQBgcqhkjOPQIBBgUrgQQAIgNiAARfD9w/q1cWxL6D9bMG
H6CQ4u+gAV6GN9s+PwQx9Bl4hC+0iU8QOk8mWO/RwXQy10DCSxT8vSIJClHKp+Ao
4qJKdYeV0SwZ7LMQziyLfxIUOY6Grja/sQFwLKYf8EdDXAyjQjBAMB0GA1UdDgQW
BBThOqshfPHjTVSu1HK3/YtZQiCQVDAOBgNVHQ8BAf8EBAMCAQYwDwYDVR0TAQH/
BAUwAwEB/zAKBggqhkjOPQQDAwNoADBlAjBhCFTkly7Yl7+s4hiw+k6ZJTXT2AiI
rvmsmfqPr5E7ecwXb6kXA5LTFd6rjwTuV3sCMQC9w6ZSbVq1mveMO6dKFziOzClT
KCT2RFT6yXtq6nzgRICgBmiXbJAXsmZ8yAwjyWc=
-----END CERTIFICATE-----`

	emOVTLSCAG3C = `-----BEGIN CERTIFICATE-----
MIIDaDCCAu6gAwIBAgIPKWkmwiejoVJjkrGUgqUEMAoGCCqGSM49BAMDMFYxCzAJ
BgNVBAYTAklOMSUwIwYDVQQKDBxlTXVkaHJhIFRlY2hub2xvZ2llcyBMaW1pdGVk
MSAwHgYDVQQDDBdlbVNpZ24gUm9vdCBUTFMgQ0EgLSBHMzAeFw0yNTA0MzAxNTM3
NDFaFw00MDA0MjgxODMwMDBaMEAxCzAJBgNVBAYTAlVTMRQwEgYDVQQKDAtlTXVk
aHJhIEluYzEbMBkGA1UEAwwSRU0gT1YgVExTIENBIC0gRzNDMHYwEAYHKoZIzj0C
AQYFK4EEACIDYgAEE4JRzVKskpjByKrZdzId65fnCb0LTKCspV3IrVHc/J0ViaFZ
fjpRIOHv1jHGPhg1ysrimGmmLhYx6KKBgatWYW3EXZGKvAnzqw5jz3kqpNztc4e+
N7ulaVSfHAKycO1no4IBljCCAZIwHwYDVR0jBBgwFoAU4TqrIXzx401UrtRyt/2L
WUIgkFQwHQYDVR0OBBYEFDTq6gzryQra+dDF4u2beMmHnhtsMB0GA1UdJQQWMBQG
CCsGAQUFBwMBBggrBgEFBQcDAjBdBgNVHSAEVjBUMDkGCysGAQQBg44hAQABMCow
KAYIKwYBBQUHAgEWHGh0dHA6Ly9yZXBvc2l0b3J5LmVtc2lnbi5jb20wDQYLKwYB
BAGDjiEBAm4wCAYGZ4EMAQICMHUGCCsGAQUFBwEBBGkwZzAkBggrBgEFBQcwAYYY
aHR0cDovL29jc3AtYy5lbXNpZ24uY29tMD8GCCsGAQUFBzAChjNodHRwOi8vcmVw
b3NpdG9yeS5lbXNpZ24uY29tL2NlcnRzL0VNT1ZUTFNDQUczQy5wN2MwNwYDVR0f
BDAwLjAsoCqgKIYmaHR0cDovL2NybC5lbXNpZ24uY29tLz9yb290dGxzY2FnMy5j
cmwwDgYDVR0PAQH/BAQDAgEGMBIGA1UdEwEB/wQIMAYBAf8CAQAwCgYIKoZIzj0E
AwMDaAAwZQIxAMSZt2xsPeumRdeSMSQ3CbzIZeQ/q7GDCWfeE1Pq+mhgA6gRM44c
NVF3xJ+wsxJk+wIwFJbaDMokD8Ei6eNOiA8yUMYvfzQyngmrhZQMdPCK1SewrR79
4rSb9vGqxZzelQth
-----END CERTIFICATE-----`

	// emOVTLSCAG3CSPKI is the SHA-256 of the intermediate's
	// SubjectPublicKeyInfo, as OkHttp 5.5.1's CertificateBlocklist lists it.
	emOVTLSCAG3CSPKI = "63ecefee431d49523bc1136c4e72d0206a477086caf606cd5cf025686c109cf8"

	compromisedHost = "bank.secure"
)

var errBlocklisted = errors.New("blocklisted certificate")

// rejectBlocklisted is the kind of check a program puts in VerifyConnection.
func rejectBlocklisted(cs tls.ConnectionState) error {
	return rejectBlocklistedCerts(cs.PeerCertificates)
}

func rejectBlocklistedCerts(certs []*x509.Certificate) error {
	for _, cert := range certs {
		sum := sha256.Sum256(cert.RawSubjectPublicKeyInfo)
		if hex.EncodeToString(sum[:]) == emOVTLSCAG3CSPKI {
			return errBlocklisted
		}
	}
	return nil
}

func TestTLSFingerprintKeepsCertificateChecks(t *testing.T) {
	root, addr, reached := serveCompromisedChain(t)

	t.Run("without a check the chain is trusted", func(t *testing.T) {
		c := clientTo(t, C().ImpersonateChrome(), addr)
		c.SetTLSClientConfig(&tls.Config{RootCAs: certPoolOf(root)})
		assertReached(t, c, reached)
	})

	t.Run("VerifyConnection sees the chain as sent", func(t *testing.T) {
		var seen tls.ConnectionState
		c := clientTo(t, C().ImpersonateChrome(), addr)
		c.SetTLSClientConfig(&tls.Config{
			RootCAs: certPoolOf(root),
			VerifyConnection: func(cs tls.ConnectionState) error {
				seen = cs
				return nil
			},
		})
		assertReached(t, c, reached)
		if seen.ServerName != compromisedHost || len(seen.PeerCertificates) != 2 || len(seen.VerifiedChains) == 0 {
			t.Fatalf("VerifyConnection saw server %q, %d certificates, %d chains; want %q, 2, at least 1",
				seen.ServerName, len(seen.PeerCertificates), len(seen.VerifiedChains), compromisedHost)
		}
	})

	t.Run("VerifyConnection", func(t *testing.T) {
		c := clientTo(t, C().ImpersonateChrome(), addr)
		c.SetTLSClientConfig(&tls.Config{RootCAs: certPoolOf(root), VerifyConnection: rejectBlocklisted})
		assertBlocked(t, c, reached)
	})

	t.Run("VerifyPeerCertificate", func(t *testing.T) {
		c := clientTo(t, C().ImpersonateChrome(), addr)
		c.SetTLSClientConfig(&tls.Config{
			RootCAs: certPoolOf(root),
			VerifyPeerCertificate: func(rawCerts [][]byte, _ [][]*x509.Certificate) error {
				var certs []*x509.Certificate
				for _, raw := range rawCerts {
					cert, err := x509.ParseCertificate(raw)
					if err != nil {
						return err
					}
					certs = append(certs, cert)
				}
				return rejectBlocklistedCerts(certs)
			},
		})
		assertBlocked(t, c, reached)
	})
}

func TestDefaultTLSClientConfig(t *testing.T) {
	root, addr, reached := serveCompromisedChain(t)
	DefaultTLSClientConfig = &tls.Config{RootCAs: certPoolOf(root), VerifyConnection: rejectBlocklisted}
	t.Cleanup(func() { DefaultTLSClientConfig = nil })

	t.Run("plain", func(t *testing.T) {
		assertBlocked(t, clientTo(t, C(), addr), reached)
	})
	t.Run("fingerprint", func(t *testing.T) {
		assertBlocked(t, clientTo(t, C().ImpersonateChrome(), addr), reached)
	})
	t.Run("Instagram Android fingerprint", func(t *testing.T) {
		assertBlocked(t, clientTo(t, C().ImpersonateInstagramAndroid(), addr), reached)
	})
	t.Run("keeps its own ALPN", func(t *testing.T) {
		if got := C().GetTLSClientConfig().NextProtos; len(got) != 2 {
			t.Fatalf("NextProtos = %q, want http/1.1 and h2", got)
		}
		if DefaultTLSClientConfig.NextProtos != nil {
			t.Fatal("creating a client changed DefaultTLSClientConfig")
		}
	})
}

// serveCompromisedChain starts a TLS server that sends a leaf issued by the
// compromised intermediate, then the intermediate, and reports whether a
// request reached its handler.
func serveCompromisedChain(t *testing.T) (root *x509.Certificate, addr string, reached *atomic.Bool) {
	t.Helper()
	root = parsePEMCert(t, emsignRootTLSCAG3)
	intermediate := parsePEMCert(t, emOVTLSCAG3C)
	intermediateKey, err := ecdsa.ParseRawPrivateKey(elliptic.P384(), big.NewInt(4).FillBytes(make([]byte, 48)))
	if err != nil {
		t.Fatalf("intermediate key: %v", err)
	}
	leafKey, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatalf("leaf key: %v", err)
	}
	der, err := x509.CreateCertificate(rand.Reader, &x509.Certificate{
		SerialNumber: big.NewInt(2),
		Subject:      pkix.Name{CommonName: compromisedHost},
		DNSNames:     []string{compromisedHost},
		NotBefore:    time.Now().Add(-time.Hour),
		NotAfter:     time.Now().Add(time.Hour),
		KeyUsage:     x509.KeyUsageDigitalSignature,
		ExtKeyUsage:  []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}, intermediate, leafKey.Public(), intermediateKey)
	if err != nil {
		t.Fatalf("issue leaf: %v", err)
	}

	reached = new(atomic.Bool)
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(http.ResponseWriter, *http.Request) {
		reached.Store(true)
	}))
	server.EnableHTTP2 = true
	server.TLS = &tls.Config{Certificates: []tls.Certificate{{
		Certificate: [][]byte{der, intermediate.Raw},
		PrivateKey:  leafKey,
	}}}
	// The rejected handshakes are expected; keep the server's reports of them out of the test log.
	server.Config.ErrorLog = log.New(io.Discard, "", 0)
	server.StartTLS()
	t.Cleanup(server.Close)
	return root, server.Listener.Addr().String(), reached
}

// clientTo sends every request c makes to addr, never through a proxy from the environment.
func clientTo(t *testing.T, c *Client, addr string) *Client {
	t.Helper()
	c.SetProxy(nil)
	c.SetDial(func(ctx context.Context, network, _ string) (net.Conn, error) {
		return (&net.Dialer{}).DialContext(ctx, network, addr)
	})
	c.SetTimeout(10 * time.Second)
	t.Cleanup(c.GetTransport().CloseIdleConnections)
	return c
}

func assertReached(t *testing.T, c *Client, reached *atomic.Bool) {
	t.Helper()
	reached.Store(false)
	if _, err := c.R().Get("https://" + compromisedHost + "/"); err != nil {
		t.Fatalf("get: %v", err)
	}
	if !reached.Load() {
		t.Fatal("the request did not reach the server")
	}
}

func assertBlocked(t *testing.T, c *Client, reached *atomic.Bool) {
	t.Helper()
	reached.Store(false)
	_, err := c.R().Get("https://" + compromisedHost + "/")
	if !errors.Is(err, errBlocklisted) {
		t.Fatalf("err = %v, want the blocklist's error", err)
	}
	if reached.Load() {
		t.Fatal("the request reached the server")
	}
}

func parsePEMCert(t *testing.T, pemText string) *x509.Certificate {
	t.Helper()
	block, _ := pem.Decode([]byte(pemText))
	if block == nil {
		t.Fatal("no PEM block")
	}
	cert, err := x509.ParseCertificate(block.Bytes)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	return cert
}

func certPoolOf(certs ...*x509.Certificate) *x509.CertPool {
	pool := x509.NewCertPool()
	for _, cert := range certs {
		pool.AddCert(cert)
	}
	return pool
}
