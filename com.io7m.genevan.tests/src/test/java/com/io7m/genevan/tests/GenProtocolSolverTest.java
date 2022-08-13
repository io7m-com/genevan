/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package com.io7m.genevan.tests;

import com.io7m.genevan.core.GenProtocolException;
import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolSolver;
import com.io7m.genevan.core.GenProtocolSolverType;
import com.io7m.genevan.core.GenProtocolVersion;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.Combinators;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import net.jqwik.api.constraints.Size;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import static com.io7m.genevan.core.GenProtocolErrorCode.AMBIGUOUS_RESULT;
import static com.io7m.genevan.core.GenProtocolErrorCode.CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON;
import static com.io7m.genevan.tests.GenProtocolHandlers.exactClient;
import static com.io7m.genevan.tests.GenProtocolHandlers.exactServer;
import static java.math.BigInteger.ONE;
import static java.math.BigInteger.TWO;
import static java.math.BigInteger.ZERO;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Tests for the protocol solver.
 */

public final class GenProtocolSolverTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(GenProtocolSolverTest.class);

  private static final String PROTOCOL_A = "com.io7m.a";
  private static final String PROTOCOL_B = "com.io7m.b";
  private static final String PROTOCOL_X = "com.io7m.x";
  private static final String PROTOCOL_Y = "com.io7m.y";
  private static final String PROTOCOL_Z = "com.io7m.z";
  private static final String PROTOCOL_W = "com.io7m.w";

  private static final GenProtocolIdentifier PROTOCOL_A_1_0 =
    new GenProtocolIdentifier(PROTOCOL_A, new GenProtocolVersion(ONE, ZERO));
  private static final GenProtocolIdentifier PROTOCOL_B_1_0 =
    new GenProtocolIdentifier(PROTOCOL_B, new GenProtocolVersion(ONE, ZERO));
  private static final GenProtocolIdentifier PROTOCOL_B_1_1 =
    new GenProtocolIdentifier(PROTOCOL_B, new GenProtocolVersion(ONE, ONE));
  private static final GenProtocolIdentifier PROTOCOL_B_1_2 =
    new GenProtocolIdentifier(PROTOCOL_B, new GenProtocolVersion(ONE, TWO));
  private GenProtocolSolverType solver;

  @Provide
  private static Arbitrary<GenProtocolIdentifier> arbitraryProtocol()
  {
    final var bmaj =
      Arbitraries.bigIntegers()
        .greaterOrEqual(ZERO);
    final var bmin =
      Arbitraries.bigIntegers()
        .greaterOrEqual(ZERO);
    final var s =
      Arbitraries.strings()
        .alpha()
        .ofMinLength(1)
        .ofMaxLength(16);
    final var vs =
      Combinators.combine(bmaj, bmin)
        .as(GenProtocolVersion::new);

    return Combinators.combine(s, vs).as(GenProtocolIdentifier::new);
  }

  @Provide
  private static Arbitrary<Set<GenProtocolIdentifier>> arbitraryProtocols()
  {
    return arbitraryProtocol().set();
  }

  @BeforeEach
  public void setup()
  {
    this.solver = GenProtocolSolver.create();
  }

  /**
   * If the server presents an empty set of protocols, solving fails.
   */

  @Test
  public void testServerNothing()
  {
    final var ex =
      assertThrows(GenProtocolException.class, () -> {
        this.solver.solve(
          Set.of(),
          Set.of(exactClient(PROTOCOL_A_1_0)),
          List.of()
        );
      });
    assertEquals(CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON, ex.errorCode());
  }

  /**
   * If the client presents an empty set of protocols, solving fails.
   */

  @Test
  public void testClientNothing()
  {
    final var ex =
      assertThrows(GenProtocolException.class, () -> {
        this.solver.solve(
          Set.of(exactServer(PROTOCOL_A_1_0)),
          Set.of(),
          List.of()
        );
      });
    assertEquals(CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON, ex.errorCode());
  }

  /**
   * If the server and client both support the one and only exact protocol, a
   * solution is found.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerClientOneExact()
    throws Exception
  {
    final var clientHandler =
      exactClient(PROTOCOL_A_1_0);
    final var serverEndpoint =
      exactServer(PROTOCOL_A_1_0);

    final var result =
      this.solver.solve(
        Set.of(serverEndpoint),
        Set.of(clientHandler),
        List.of()
      );

    assertEquals(clientHandler, result.clientHandler());
    assertEquals(serverEndpoint, result.serverEndpoint());
  }

  /**
   * If the server and client both support the one and only exact protocol, a
   * solution is found.
   *
   * @throws Exception On errors
   */

  @Property
  public void testServerClientOneExactP(
    final @ForAll("arbitraryProtocol") GenProtocolIdentifier p)
    throws Exception
  {
    this.solver = GenProtocolSolver.create();

    final var server =
      exactServer(p);
    final var client =
      exactClient(p);

    final var result =
      this.solver.solve(
        Set.of(server),
        Set.of(client),
        List.of()
      );

    assertEquals(client, result.clientHandler());
    assertEquals(server, result.serverEndpoint());
  }

  /**
   * If the client supports everything the server provides, and no preferences
   * are provided, then the result is ambiguous.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerClientAmbiguous()
    throws Exception
  {
    final var clients =
      Set.of(
        exactClient(PROTOCOL_A_1_0),
        exactClient(PROTOCOL_B_1_0)
      );

    final var servers =
      Set.of(
        exactServer(PROTOCOL_A_1_0),
        exactServer(PROTOCOL_B_1_0)
      );

    final var ex =
      assertThrows(GenProtocolException.class, () -> {
        this.solver.solve(
          servers,
          clients,
          List.of()
        );
      });
    assertEquals(AMBIGUOUS_RESULT, ex.errorCode());
    LOG.debug("{}", ex.getMessage());
  }

  /**
   * If the client supports everything the server provides, assuming the server
   * provides more than one thing, a client that supports all the same
   * protocols cannot disambiguate without preferences.
   *
   * @throws Exception On errors
   */

  @Property
  public void testServerClientAmbiguousP(
    final @ForAll("arbitraryProtocols") @Size(min = 2) Set<GenProtocolIdentifier> serverSupportsIn)
    throws Exception
  {
    this.solver = GenProtocolSolver.create();

    /*
     * We need to add an extra protocol because there's no guarantee
     * that the generated serverSupportsIn set will actually contain
     * different protocol names (and therefore, ambiguity!).
     */

    final var serverSupports = new HashSet<>(serverSupportsIn);
    serverSupports.add(new GenProtocolIdentifier(
      "EXTRA!",
      new GenProtocolVersion(ONE, ZERO)
    ));

    final var serverEndpoints =
      serverSupports.stream()
        .map(GenProtocolHandlers::exactServer)
        .collect(Collectors.toUnmodifiableSet());

    final var clientHandlers =
      serverSupports.stream()
        .map(GenProtocolHandlers::exactClient)
        .collect(Collectors.toUnmodifiableSet());

    final var ex =
      assertThrows(GenProtocolException.class, () -> {
        final var r = this.solver.solve(
          serverEndpoints,
          clientHandlers,
          List.of()
        );
        LOG.debug("r: {}", r);
      });
    assertEquals(AMBIGUOUS_RESULT, ex.errorCode());
  }

  /**
   * If the client supports everything the server provides, and useless
   * preferences are provided, then the result is ambiguous.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerClientAmbiguousUselessPreferences()
    throws Exception
  {
    final var clientHandlers =
      Set.of(
        exactClient(PROTOCOL_A_1_0),
        exactClient(PROTOCOL_B_1_0)
      );

    final var serverEndpoints =
      Set.of(
        exactServer(PROTOCOL_A_1_0),
        exactServer(PROTOCOL_B_1_0)
      );

    final var ex =
      assertThrows(GenProtocolException.class, () -> {
        this.solver.solve(
          serverEndpoints,
          clientHandlers,
          List.of(PROTOCOL_X, PROTOCOL_Y, PROTOCOL_Z, PROTOCOL_W)
        );
      });
    assertEquals(AMBIGUOUS_RESULT, ex.errorCode());
    LOG.debug("{}", ex.getMessage());
  }

  /**
   * If the server and client do not have a protocol in common, the result is an
   * error.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerClientNoCommon0()
    throws Exception
  {
    final var clientHandlers =
      Set.of(
        exactClient(PROTOCOL_A_1_0)
      );

    final var serverEndpoints =
      Set.of(
        exactServer(PROTOCOL_B_1_0)
      );

    final var ex =
      assertThrows(GenProtocolException.class, () -> {
        this.solver.solve(
          serverEndpoints,
          clientHandlers,
          List.of()
        );
      });
    assertEquals(CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON, ex.errorCode());
    LOG.debug("{}", ex.getMessage());
  }

  /**
   * The server presents versions with one obvious best choice.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerClientObvious0()
    throws Exception
  {
    final var clientHandlers =
      Set.of(
        exactClient(PROTOCOL_B_1_0),
        exactClient(PROTOCOL_B_1_1),
        exactClient(PROTOCOL_B_1_2)
      );

    final var serverEndpoints =
      Set.of(
        exactServer(PROTOCOL_A_1_0),
        exactServer(PROTOCOL_B_1_0)
      );

    final var result =
      this.solver.solve(
        serverEndpoints,
        clientHandlers,
        List.of()
      );

    assertEquals(exactClient(PROTOCOL_B_1_2), result.clientHandler());
    assertEquals(exactServer(PROTOCOL_B_1_0), result.serverEndpoint());
  }

  /**
   * If the client supports everything the server provides, the client can
   * disambiguate with a preferred protocol.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerClientAmbiguousPreferred()
    throws Exception
  {
    final var clientHandlers =
      Set.of(
        exactClient(PROTOCOL_A_1_0),
        exactClient(PROTOCOL_B_1_0)
      );

    final var serverEndpoints =
      Set.of(
        exactServer(PROTOCOL_A_1_0),
        exactServer(PROTOCOL_B_1_0)
      );

    final var result =
      this.solver.solve(
        serverEndpoints,
        clientHandlers,
        List.of(PROTOCOL_B)
      );

    assertEquals(exactClient(PROTOCOL_B_1_0), result.clientHandler());
    assertEquals(exactServer(PROTOCOL_B_1_0), result.serverEndpoint());
  }

  /**
   * If the client supports everything the server provides, assuming the server
   * provides more than one thing, a client that supports all of the same
   * protocols cannot disambiguate without preferences.
   *
   * @throws Exception On errors
   */

  @Property
  public void testServerClientAmbiguousPreferredP(
    final @ForAll("arbitraryProtocols") @Size(min = 2) Set<GenProtocolIdentifier> serverSupportsIn)
    throws Exception
  {
    this.solver = GenProtocolSolver.create();

    /*
     * We need to add an extra protocol because there's no guarantee
     * that the generated serverSupportsIn set will actually contain
     * different protocol names (and therefore, ambiguity!).
     */

    final var serverSupports = new HashSet<>(serverSupportsIn);
    serverSupports.add(new GenProtocolIdentifier(
      "EXTRA!",
      new GenProtocolVersion(ONE, ZERO)
    ));

    /*
     * Pick an arbitrary protocol name from the set.
     */

    final var preferred =
      serverSupports.stream()
        .map(GenProtocolIdentifier::identifier)
        .findFirst()
        .orElseThrow();

    /*
     * The expected handler is the handler that supports the preferred
     * protocol with the highest version number.
     */

    final var expected =
      serverSupports.stream()
        .filter(p -> Objects.equals(p.identifier(), preferred))
        .max(Comparator.comparing(GenProtocolIdentifier::version))
        .map(GenProtocolHandlers::exactClient)
        .orElseThrow();

    final var serverEndpoints =
      serverSupports.stream()
        .map(GenProtocolHandlers::exactServer)
        .collect(Collectors.toUnmodifiableSet());

    final var clientHandlers =
      serverSupports.stream()
        .map(GenProtocolHandlers::exactClient)
        .collect(Collectors.toUnmodifiableSet());

    final var result =
      this.solver.solve(
        serverEndpoints,
        clientHandlers,
        List.of(preferred)
      );

    assertEquals(expected, result.clientHandler());
  }

  /**
   * If the client supports everything the server provides, the client can
   * disambiguate with a preferred protocol.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerClientAmbiguousPreferredExtras()
    throws Exception
  {
    final var clientHandlers =
      Set.of(
        exactClient(PROTOCOL_A_1_0),
        exactClient(PROTOCOL_B_1_0)
      );

    final var serverEndpoints =
      Set.of(
        exactServer(PROTOCOL_A_1_0),
        exactServer(PROTOCOL_B_1_0)
      );

    final var result =
      this.solver.solve(
        serverEndpoints,
        clientHandlers,
        List.of(PROTOCOL_X, PROTOCOL_Y, PROTOCOL_Z, PROTOCOL_B, PROTOCOL_W)
      );

    assertEquals(exactClient(PROTOCOL_B_1_0), result.clientHandler());
    assertEquals(exactServer(PROTOCOL_B_1_0), result.serverEndpoint());
  }
}
